#!/usr/bin/env python3
"""Syntactic mutation stage: derive incorrect outputs from cargo-mutants edits.

This runs after semantic (LLM) mutation and before direct output mutation. It
enumerates local AST edits of ``code.rs`` with cargo-mutants -- operator swaps,
negated conditionals, and return-value replacements -- then compiles each mutant
against the problem harness and records the inputs whose outputs disagree with
the reference, using the same per-input deduplication as the semantic stage.

cargo-mutants is used only as a mutation *enumerator*, via ``--Zmutate-file``,
which mutates a standalone file without needing a cargo workspace. Each listed
mutant carries a source span and a replacement string, so we apply the edit
ourselves and reuse the existing harness compile/run path rather than letting
cargo-mutants drive a test suite.

Per problem, output is written to:

    cache/<pid>/incorrect_syntactic.jsonl  -- {"input": ..., "output": <wrong>, "_src": "<mutant name>"}
    cache/<pid>/syntactic.log              -- enumeration/compile/run notes

Usage:
    python3 syntactic_mutator.py run --problems lc121 lc2404
    python3 syntactic_mutator.py run --workers 8
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from harness_utils import (  # noqa: E402
    LEETCODE_DIR,
    assemble_variant_source,
    compile_rust,
    parse_output_field,
    run_binary_with_inputs,
    with_temp_workdir,
)

CACHE_DIR = Path(__file__).resolve().parent / "cache"

# Multiple of the positive-set size that the code-mutant stages (semantic +
# syntactic) together aim for. Direct output mutation covers the rest.
CODE_MUTANT_MULTIPLIER = 8


def _canon(value) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False)


def _read_jsonl(path: Path) -> list[dict]:
    out = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out


def list_mutants(source: Path, *, timeout: float = 120.0) -> list[dict]:
    """Enumerate cargo-mutants edits for a standalone Rust file.

    Returns the raw mutant descriptors; each has ``name``, ``replacement`` and a
    ``span`` with 1-based line/column start and end.
    """
    cmd = [
        "cargo",
        "mutants",
        "--Zmutate-file",
        str(source),
        "--list",
        "--json",
    ]
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=source.parent,
        )
    except FileNotFoundError:
        raise RuntimeError("cargo-mutants not found on PATH")
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"cargo mutants --list timed out ({timeout}s)")
    if proc.returncode != 0:
        raise RuntimeError(f"cargo mutants --list failed: {(proc.stderr or '')[:500]}")
    try:
        return json.loads(proc.stdout or "[]")
    except json.JSONDecodeError as e:
        raise RuntimeError(f"cargo mutants --list emitted invalid JSON: {e}")


def apply_mutant(source_text: str, mutant: dict) -> str | None:
    """Apply one cargo-mutants edit to ``source_text``.

    The span is 1-based in both line and column, with the end column exclusive,
    and columns index characters rather than bytes. Returns None if the span
    does not fit the source, which keeps a malformed descriptor from silently
    corrupting the file.
    """
    span = mutant.get("span") or {}
    start = span.get("start") or {}
    end = span.get("end") or {}
    replacement = mutant.get("replacement")
    if replacement is None:
        return None
    try:
        sl, sc = int(start["line"]), int(start["column"])
        el, ec = int(end["line"]), int(end["column"])
    except (KeyError, TypeError, ValueError):
        return None

    lines = source_text.splitlines(keepends=True)
    if not (1 <= sl <= len(lines) and 1 <= el <= len(lines)):
        return None
    # Convert (line, column) to an absolute offset.
    offsets = []
    acc = 0
    for ln in lines:
        offsets.append(acc)
        acc += len(ln)
    try:
        start_off = offsets[sl - 1] + (sc - 1)
        end_off = offsets[el - 1] + (ec - 1)
    except IndexError:
        return None
    if not (0 <= start_off <= end_off <= len(source_text)):
        return None
    return source_text[:start_off] + replacement + source_text[end_off:]


def run_one_problem(
    pid: str,
    *,
    timeout: float,
    compile_timeout: float,
    list_timeout: float,
    max_mutants: int,
    target: int | None = None,
) -> dict:
    """Collect incorrect outputs from cargo-mutants edits of one problem.

    ``target`` caps how many negative cases to gather; when the semantic stage
    already reached the 8x budget there is nothing left for this stage to do.
    """
    pdir = LEETCODE_DIR / pid
    cache_pdir = CACHE_DIR / pid
    log: list[str] = []
    try:
        harness = (pdir / "tests" / "harness.rs").read_text()
        code_src = (pdir / "code.rs").read_text()
        testcases = _read_jsonl(pdir / "tests" / "testcases.jsonl")
    except FileNotFoundError as e:
        return {"pid": pid, "ok": False, "error": str(e)}
    if not testcases:
        return {"pid": pid, "ok": False, "error": "empty testcases"}

    if target is None:
        target = CODE_MUTANT_MULTIPLIER * len(testcases)

    # Dedup against whatever the semantic stage already contributed, so the two
    # code-mutant stages do not double-count the same (input, wrong output).
    seen: set[tuple[str, str]] = set()
    llm_path = cache_pdir / "incorrect_llm.jsonl"
    n_llm = 0
    if llm_path.exists():
        for r in _read_jsonl(llm_path):
            seen.add((_canon(r["input"]), _canon(r["output"])))
            n_llm += 1

    remaining = target - n_llm
    if remaining <= 0:
        cache_pdir.mkdir(parents=True, exist_ok=True)
        (cache_pdir / "incorrect_syntactic.jsonl").write_text("")
        (cache_pdir / "syntactic.log").write_text(
            f"semantic stage already at/over the {target} target (n={n_llm}); skipped\n"
        )
        return {"pid": pid, "ok": True, "incorrect": 0, "skipped": "target_met", "llm": n_llm}

    input_lines = [json.dumps(rec, ensure_ascii=False) for rec in testcases]
    ref_outputs = [rec["output"] for rec in testcases]

    incorrect: list[dict] = []
    n_compile_fail = 0
    n_run_fail = 0
    n_apply_fail = 0
    n_retained = 0
    n_rejected_all_pass = 0
    n_rejected_all_fail = 0

    with with_temp_workdir(prefix="vcg_synmut_") as td:
        td_path = Path(td)
        code_copy = td_path / "code.rs"
        code_copy.write_text(code_src)
        try:
            mutants = list_mutants(code_copy, timeout=list_timeout)
        except RuntimeError as e:
            return {"pid": pid, "ok": False, "error": str(e)}
        log.append(f"cargo-mutants enumerated {len(mutants)} mutants")
        if max_mutants:
            mutants = mutants[:max_mutants]

        for idx, mutant in enumerate(mutants):
            if len(incorrect) >= remaining:
                log.append(f"reached remaining budget ({remaining}); stopping early")
                break
            name = mutant.get("name", f"mutant_{idx}")
            mutated_code = apply_mutant(code_src, mutant)
            if mutated_code is None:
                log.append(f"{name}: could not apply span; skipped")
                n_apply_fail += 1
                continue
            try:
                src = assemble_variant_source(harness, mutated_code)
            except Exception as e:
                log.append(f"{name}: assemble error: {e}")
                n_compile_fail += 1
                continue
            stem = f"mutant_{idx}"
            sp = td_path / f"{stem}.rs"
            bp = td_path / stem
            sp.write_text(src)
            ok, msg = compile_rust(sp, bp, timeout=compile_timeout)
            if not ok:
                # Mutants that do not typecheck are expected and uninteresting.
                log.append(f"{name}: compile failed: {msg.splitlines()[0][:200] if msg else ''}")
                n_compile_fail += 1
                continue
            ok2, out_lines, err = run_binary_with_inputs(bp, input_lines, timeout=timeout)
            if not out_lines:
                log.append(f"{name}: run produced no output (rc_ok={ok2}); err={err[:200]}")
                n_run_fail += 1
                continue

            v_candidates: list[tuple[tuple[str, str], dict]] = []
            v_match = 0
            v_diff = 0
            for i, line in enumerate(out_lines):
                if i >= len(ref_outputs):
                    break
                got = parse_output_field(line)
                if got is None:
                    continue
                if _canon(got) == _canon(ref_outputs[i]):
                    v_match += 1
                    continue
                v_diff += 1
                key = (_canon(testcases[i]["input"]), _canon(got))
                v_candidates.append(
                    (key, {"input": testcases[i]["input"], "output": got, "_src": name})
                )

            # Same retention rule as the semantic stage: a mutant is only useful
            # when it is partially wrong.
            evaluated = v_match + v_diff
            if evaluated == 0:
                n_run_fail += 1
                continue
            if v_diff == 0:
                n_rejected_all_pass += 1
                continue
            if v_match == 0:
                n_rejected_all_fail += 1
                continue

            n_retained += 1
            for key, rec in v_candidates:
                if key in seen:
                    continue
                seen.add(key)
                incorrect.append(rec)
                if len(incorrect) >= remaining:
                    break

    cache_pdir.mkdir(parents=True, exist_ok=True)
    with open(cache_pdir / "incorrect_syntactic.jsonl", "w") as f:
        for r in incorrect:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    (cache_pdir / "syntactic.log").write_text("\n".join(log) + "\n")

    return {
        "pid": pid,
        "ok": True,
        "incorrect": len(incorrect),
        "llm": n_llm,
        "target": target,
        "mutants": len(mutants),
        "retained": n_retained,
        "compile_fail": n_compile_fail,
        "run_fail": n_run_fail,
        "apply_fail": n_apply_fail,
        "rejected_all_pass": n_rejected_all_pass,
        "rejected_all_fail": n_rejected_all_fail,
    }


def cmd_run(args: argparse.Namespace) -> int:
    if args.problems:
        pids = args.problems
    else:
        pids = sorted(
            p.name
            for p in LEETCODE_DIR.iterdir()
            if p.is_dir()
            and p.name.startswith("lc")
            and (p / "tests" / "testcases.jsonl").exists()
            and (p / "tests" / "harness.rs").exists()
        )
    if args.limit:
        pids = pids[: args.limit]
    if not pids:
        print("no problems found")
        return 1

    kwargs = dict(
        timeout=args.timeout,
        compile_timeout=args.compile_timeout,
        list_timeout=args.list_timeout,
        max_mutants=args.max_mutants,
    )

    results: list[dict] = []
    if args.workers <= 1:
        for pid in pids:
            res = run_one_problem(pid, **kwargs)
            print(json.dumps(res, ensure_ascii=False))
            results.append(res)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as ex:
            futs = {ex.submit(run_one_problem, pid, **kwargs): pid for pid in pids}
            for fut in as_completed(futs):
                try:
                    res = fut.result()
                except Exception as e:
                    res = {"pid": futs[fut], "ok": False, "error": f"{type(e).__name__}: {e}"}
                print(json.dumps(res, ensure_ascii=False))
                results.append(res)

    n_ok = sum(1 for r in results if r.get("ok"))
    total = sum(r.get("incorrect", 0) for r in results if r.get("ok"))
    print(f"summary: ok={n_ok}/{len(results)} total_syntactic_cases={total}")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(
        description="Collect incorrect outputs from cargo-mutants syntactic mutants"
    )
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="Run syntactic mutation for problems")
    r.add_argument("--problems", nargs="*", help="Problem IDs (default: all leetcode)")
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("--workers", type=int, default=4)
    r.add_argument("--timeout", type=float, default=120.0, help="seconds for the binary run")
    r.add_argument("--compile-timeout", type=float, default=120.0)
    r.add_argument("--list-timeout", type=float, default=120.0)
    r.add_argument(
        "--max-mutants",
        type=int,
        default=200,
        help="cap on mutants evaluated per problem (0 = no cap)",
    )
    r.set_defaults(func=cmd_run)
    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

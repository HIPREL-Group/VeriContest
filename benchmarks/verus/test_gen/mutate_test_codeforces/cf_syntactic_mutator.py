#!/usr/bin/env python3
"""Syntactic mutation stage for Codeforces: incorrect outputs from cargo-mutants.

Codeforces counterpart of ``mutate_test_leetcode/syntactic_mutator.py``. It runs
after semantic (LLM) mutation and before direct output mutation, enumerating
local AST edits of ``code.rs`` with cargo-mutants -- operator swaps, negated
conditionals, and return-value replacements -- then splicing each mutant into the
problem's ``main.rs`` and recording the inputs whose stdout disagrees with the
reference, with the same per-input deduplication as the semantic stage.

cargo-mutants is used only as a mutation *enumerator*, via ``--Zmutate-file``.
Each listed mutant carries a source span and a replacement string, so we apply
the edit ourselves and reuse the existing compile/run path.

Per problem, output is written to:

    cache/<pid>/incorrect_syntactic.jsonl  -- {"input": "...", "output": "<wrong stdout>"}
    cache/<pid>/syntactic.log              -- enumeration/compile/run notes

Usage:
    python3 cf_syntactic_mutator.py run --problems cf1006C
    python3 cf_syntactic_mutator.py run --workers 8
"""
from __future__ import annotations

import argparse
import json
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cf_harness_utils import (  # noqa: E402
    CF_DIR,
    assemble_variant_main,
    compile_rust,
    normalize_output,
    run_binary,
)

# cargo-mutants enumeration/application logic is shared with the leetcode stage.
sys.path.insert(
    0, str(Path(__file__).resolve().parent.parent / "mutate_test_leetcode")
)
from syntactic_mutator import apply_mutant, list_mutants  # noqa: E402

CACHE_DIR = Path(__file__).resolve().parent / "cache"

# Multiple of the positive-set size that the code-mutant stages (semantic +
# syntactic) together aim for. Direct output mutation covers the rest.
CODE_MUTANT_MULTIPLIER = 8


def _read_jsonl(path: Path) -> list[dict]:
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


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
    pdir = CF_DIR / pid
    cache_pdir = CACHE_DIR / pid
    log: list[str] = []
    try:
        main_src = (pdir / "main.rs").read_text()
        code_src = (pdir / "code.rs").read_text()
        testcases = _read_jsonl(pdir / "tests" / "testcases.jsonl")
    except FileNotFoundError as e:
        return {"pid": pid, "ok": False, "error": str(e)}
    if not testcases:
        return {"pid": pid, "ok": False, "error": "empty testcases"}

    if target is None:
        target = CODE_MUTANT_MULTIPLIER * len(testcases)

    # Dedup against whatever the semantic stage already contributed.
    seen: set[tuple[str, str]] = set()
    llm_path = cache_pdir / "incorrect_llm.jsonl"
    n_llm = 0
    if llm_path.exists():
        for r in _read_jsonl(llm_path):
            seen.add((r["input"], r["output"]))
            n_llm += 1

    remaining = target - n_llm
    if remaining <= 0:
        cache_pdir.mkdir(parents=True, exist_ok=True)
        (cache_pdir / "incorrect_syntactic.jsonl").write_text("")
        (cache_pdir / "syntactic.log").write_text(
            f"semantic stage already at/over the {target} target (n={n_llm}); skipped\n"
        )
        return {"pid": pid, "ok": True, "incorrect": 0, "skipped": "target_met", "llm": n_llm}

    incorrect: list[dict] = []
    n_compile_fail = 0
    n_run_fail = 0
    n_apply_fail = 0
    n_timeout = 0
    n_retained = 0
    n_rejected_all_pass = 0
    n_rejected_all_fail = 0

    with tempfile.TemporaryDirectory(prefix="vcg_cfsynmut_") as td:
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
                src = assemble_variant_main(main_src, mutated_code)
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

            v_candidates: list[tuple[tuple[str, str], dict]] = []
            v_match = 0
            v_diff = 0
            for tc in testcases:
                ok2, stdout, err = run_binary(bp, tc["input"], timeout=timeout)
                if not ok2 and "timed out" in err:
                    n_timeout += 1
                    continue
                if not ok2 and not stdout:
                    n_run_fail += 1
                    continue
                if normalize_output(stdout) == normalize_output(tc["output"]):
                    v_match += 1
                    continue
                v_diff += 1
                v_candidates.append(
                    ((tc["input"], stdout), {"input": tc["input"], "output": stdout})
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
        "timeout": n_timeout,
        "rejected_all_pass": n_rejected_all_pass,
        "rejected_all_fail": n_rejected_all_fail,
    }


def cmd_run(args: argparse.Namespace) -> int:
    if args.problems:
        pids = args.problems
    else:
        pids = sorted(
            p.name
            for p in CF_DIR.iterdir()
            if p.is_dir()
            and p.name.startswith("cf")
            and (p / "tests" / "testcases.jsonl").exists()
            and (p / "main.rs").exists()
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
        description="Collect incorrect Codeforces outputs from cargo-mutants syntactic mutants"
    )
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="Run syntactic mutation for problems")
    r.add_argument("--problems", nargs="*", help="Problem IDs (default: all codeforces)")
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("--workers", type=int, default=4)
    r.add_argument("--timeout", type=float, default=10.0, help="seconds per testcase run")
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

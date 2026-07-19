#!/usr/bin/env python3
"""End-to-end mutator for Codeforces: combine code-mutant outputs with the
symbolic mutator until each problem reaches ``multiplier x`` of its original
testcase count. Writes ``tests/mutated_testcases.jsonl`` per problem.

Code mutants (semantic + syntactic) are collected first, up to
``code_multiplier x`` of the positive set; direct output mutation then fills the
remaining gap to the full ``multiplier x`` target:

    semantic    = cache/<pid>/incorrect_llm.jsonl        (may not exist yet)
    syntactic   = cache/<pid>/incorrect_syntactic.jsonl  (may not exist yet)
    code_target = N * code_multiplier      (default 8x)
    target      = N * multiplier           (default 10x)

By default only problems **without** ``tests/mutated_testcases.jsonl`` are
processed. Pass ``--include-with-mutated`` to regenerate for all (or for the
subset given by ``--problems``).

Each line: {"input": "<stdin string>", "output": "<wrong stdout string>"}.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cf_harness_utils import CF_DIR, list_codeforces_problems  # noqa: E402
from cf_symbolic_mutator import expand_to_target  # noqa: E402

CACHE_DIR = Path(__file__).resolve().parent / "cache"


def _canon(value) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False)


def _read_jsonl(path: Path) -> list[dict]:
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def _write_jsonl(path: Path, records: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")


def mutate_problem(
    pid: str, *, multiplier: int, code_multiplier: int, seed: int, out_name: str
) -> dict:
    pdir = CF_DIR / pid
    cases_path = pdir / "tests" / "testcases.jsonl"
    if not cases_path.exists():
        return {"pid": pid, "ok": False, "error": "no testcases.jsonl"}
    originals = _read_jsonl(cases_path)
    if not originals:
        return {"pid": pid, "ok": False, "error": "empty testcases"}
    target = multiplier * len(originals)
    code_target = code_multiplier * len(originals)

    ref_by_input: dict[str, str] = {
        _canon(r["input"]): _canon(r["output"]) for r in originals
    }

    seen: set[tuple[str, str]] = set()

    def collect(path: Path, budget: int) -> list[dict]:
        """Read a code-mutant cache file, dropping cases that are not usable
        negatives: inputs outside the positive set, outputs equal to the
        reference, and duplicates already taken by an earlier stage."""
        out: list[dict] = []
        if not path.exists():
            return out
        for r in _read_jsonl(path):
            if len(out) >= budget:
                break
            inp_key = _canon(r["input"])
            out_key = _canon(r["output"])
            if inp_key not in ref_by_input:
                continue
            if out_key == ref_by_input[inp_key]:
                continue
            key = (inp_key, out_key)
            if key in seen:
                continue
            seen.add(key)
            out.append({"input": r["input"], "output": r["output"]})
        return out

    # Stage 1: semantic (LLM) mutants, capped at the code-mutant budget.
    llm_records = collect(CACHE_DIR / pid / "incorrect_llm.jsonl", code_target)
    # Stage 2: syntactic (cargo-mutants) mutants top up toward the same budget.
    syn_records = collect(
        CACHE_DIR / pid / "incorrect_syntactic.jsonl",
        code_target - len(llm_records),
    )
    code_records = llm_records + syn_records

    rng = random.Random(seed)
    # Stage 3: direct output mutation fills the gap to the full target.
    symbolic = expand_to_target(originals, target, rng, existing=code_records)
    sym_records = [{"input": r["input"], "output": r["output"]} for r in symbolic]

    combined = code_records + sym_records
    if len(combined) > target:
        combined = combined[:target]

    out_path = pdir / "tests" / out_name
    _write_jsonl(out_path, combined)
    return {
        "pid": pid,
        "ok": True,
        "original": len(originals),
        "target": target,
        "code_target": code_target,
        "llm": len(llm_records),
        "syntactic": len(syn_records),
        "symbolic": len(sym_records),
        "total": len(combined),
        "out": str(out_path.relative_to(CF_DIR.parent.parent)),
    }


def cmd_run(args: argparse.Namespace) -> int:
    problems = list_codeforces_problems(
        only_missing_mutated=not args.include_with_mutated,
    )
    if args.problems:
        wanted = set(args.problems)
        pids = [p.name for p in problems if p.name in wanted]
    else:
        pids = [p.name for p in problems]
    if args.limit:
        pids = pids[: args.limit]

    results: list[dict] = []
    if args.workers <= 1:
        for pid in pids:
            res = mutate_problem(
                pid,
                multiplier=args.multiplier,
                code_multiplier=args.code_multiplier,
                seed=args.seed,
                out_name=args.out_name,
            )
            print(json.dumps(res, ensure_ascii=False))
            results.append(res)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as ex:
            futs = {
                ex.submit(
                    mutate_problem,
                    pid,
                    multiplier=args.multiplier,
                    code_multiplier=args.code_multiplier,
                    seed=args.seed,
                    out_name=args.out_name,
                ): pid
                for pid in pids
            }
            for fut in as_completed(futs):
                try:
                    res = fut.result()
                except Exception as e:
                    res = {"pid": futs[fut], "ok": False, "error": f"{type(e).__name__}: {e}"}
                print(json.dumps(res, ensure_ascii=False))
                results.append(res)

    n_ok = sum(1 for r in results if r.get("ok"))
    n_short = sum(1 for r in results if r.get("ok") and r.get("total", 0) < r.get("target", 0))
    sum_total = sum(r.get("total", 0) for r in results if r.get("ok"))
    print(f"summary: ok={n_ok}/{len(results)} short_of_target={n_short} total_mutated={sum_total}")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(
        description="Combine code-mutant + direct output mutations to N x originals (Codeforces)"
    )
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--problems", nargs="*")
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("--multiplier", type=int, default=10)
    r.add_argument(
        "--code-multiplier",
        type=int,
        default=8,
        help="multiple of the positive set reserved for semantic + syntactic code mutants",
    )
    r.add_argument("--seed", type=int, default=0)
    r.add_argument("--workers", type=int, default=4)
    r.add_argument("--out-name", default="mutated_testcases.jsonl")
    r.add_argument(
        "--include-with-mutated",
        action="store_true",
        help="Also process problems that already have tests/mutated_testcases.jsonl "
        "(default: only problems without that file).",
    )
    r.set_defaults(func=cmd_run)
    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

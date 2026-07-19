#!/usr/bin/env python3
"""Compile cache/<pid>/variant_*.rs against each problem's harness, run on
``testcases.jsonl``, and emit the cases whose output differs from the reference.

A variant is *retained* only when its pass rate on the positive set lies
strictly between 0% and 100%. A variant that passes everything carries no bug
we can observe, and one that fails everything is trivially broken rather than
subtly buggy; neither is a useful source of negative cases. Only retained
variants contribute their disagreeing outputs.

Per problem, output is written to:

    cache/<pid>/incorrect_llm.jsonl   -- {"input": ..., "output": <wrong>, "_src": "variant_K"}
    cache/<pid>/run.log                -- compile/run notes for debugging

Each input row appears at most once per variant (we keep the first wrong output
per input from each variant, deduped on (input, wrong-output) across variants).
"""
from __future__ import annotations

import argparse
import json
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


def run_one_problem(
    pid: str,
    *,
    timeout: float,
    compile_timeout: float,
) -> dict:
    pdir = LEETCODE_DIR / pid
    cache_pdir = CACHE_DIR / pid
    log: list[str] = []
    try:
        harness = (pdir / "tests" / "harness.rs").read_text()
        testcases = _read_jsonl(pdir / "tests" / "testcases.jsonl")
    except FileNotFoundError as e:
        return {"pid": pid, "ok": False, "error": str(e)}
    if not testcases:
        return {"pid": pid, "ok": False, "error": "empty testcases"}

    # The harness's get_field() does substring matching, so we can feed the
    # raw JSONL lines unchanged: nested {"input":{...}} fields like "nums" and
    # "target" still resolve to the right values.
    input_lines = [json.dumps(rec, ensure_ascii=False) for rec in testcases]
    ref_outputs = [rec["output"] for rec in testcases]

    variants = sorted(cache_pdir.glob("variant_*.rs"))
    if not variants:
        return {"pid": pid, "ok": False, "error": "no variants in cache"}

    incorrect: list[dict] = []
    seen: set[tuple[str, str]] = set()
    n_compile_fail = 0
    n_run_fail = 0
    n_diff = 0
    n_match = 0
    n_unknown = 0
    n_retained = 0
    n_rejected_all_pass = 0
    n_rejected_all_fail = 0

    with with_temp_workdir() as td:
        td_path = Path(td)
        for vp in variants:
            try:
                variant_code = vp.read_text()
                src = assemble_variant_source(harness, variant_code)
            except Exception as e:
                log.append(f"{vp.name}: assemble error: {e}")
                n_compile_fail += 1
                continue
            sp = td_path / f"{vp.stem}.rs"
            bp = td_path / vp.stem
            sp.write_text(src)
            ok, msg = compile_rust(sp, bp, timeout=compile_timeout)
            if not ok:
                log.append(f"{vp.name}: compile failed:\n{msg[:1500]}")
                n_compile_fail += 1
                continue
            ok2, out_lines, err = run_binary_with_inputs(bp, input_lines, timeout=timeout)
            if not out_lines:
                log.append(f"{vp.name}: run produced no output (rc_ok={ok2}); err={err[:500]}")
                n_run_fail += 1
                continue
            # Stage this variant's results; whether they count depends on the
            # variant's overall pass rate, which we only know after the loop.
            v_candidates: list[tuple[tuple[str, str], dict]] = []
            v_match = 0
            v_diff = 0
            v_unknown = 0
            for i, line in enumerate(out_lines):
                if i >= len(ref_outputs):
                    break
                got = parse_output_field(line)
                if got is None:
                    v_unknown += 1
                    continue
                if _canon(got) == _canon(ref_outputs[i]):
                    v_match += 1
                    continue
                v_diff += 1
                key = (_canon(testcases[i]["input"]), _canon(got))
                v_candidates.append(
                    (key, {"input": testcases[i]["input"], "output": got, "_src": vp.stem})
                )

            n_match += v_match
            n_diff += v_diff
            n_unknown += v_unknown

            # Retain only if the pass rate is strictly between 0% and 100%.
            evaluated = v_match + v_diff
            if evaluated == 0:
                log.append(f"{vp.name}: no comparable outputs; dropped")
                n_run_fail += 1
                continue
            if v_diff == 0:
                log.append(f"{vp.name}: pass rate 100% (no bug observed); dropped")
                n_rejected_all_pass += 1
                continue
            if v_match == 0:
                log.append(f"{vp.name}: pass rate 0% (trivially broken); dropped")
                n_rejected_all_fail += 1
                continue

            n_retained += 1
            log.append(
                f"{vp.name}: retained, pass rate {v_match}/{evaluated} "
                f"({100.0 * v_match / evaluated:.1f}%)"
            )
            for key, rec in v_candidates:
                if key in seen:
                    continue
                seen.add(key)
                incorrect.append(rec)

    cache_pdir.mkdir(parents=True, exist_ok=True)
    out_path = cache_pdir / "incorrect_llm.jsonl"
    with open(out_path, "w") as f:
        for r in incorrect:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    (cache_pdir / "run.log").write_text("\n".join(log) + "\n")

    return {
        "pid": pid,
        "ok": True,
        "incorrect": len(incorrect),
        "compile_fail": n_compile_fail,
        "run_fail": n_run_fail,
        "diff": n_diff,
        "match": n_match,
        "unknown": n_unknown,
        "variants": len(variants),
        "retained": n_retained,
        "rejected_all_pass": n_rejected_all_pass,
        "rejected_all_fail": n_rejected_all_fail,
    }


def cmd_run(args: argparse.Namespace) -> int:
    if args.problems:
        pids = args.problems
    else:
        pids = sorted(p.name for p in CACHE_DIR.iterdir() if p.is_dir() and p.name.startswith("lc"))
    if args.limit:
        pids = pids[: args.limit]
    if not pids:
        print("no problem ids found in cache/")
        return 1

    if args.workers <= 1:
        for pid in pids:
            res = run_one_problem(pid, timeout=args.timeout, compile_timeout=args.compile_timeout)
            print(json.dumps(res, ensure_ascii=False))
        return 0

    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = {
            ex.submit(
                run_one_problem,
                pid,
                timeout=args.timeout,
                compile_timeout=args.compile_timeout,
            ): pid
            for pid in pids
        }
        for fut in as_completed(futs):
            try:
                res = fut.result()
            except Exception as e:
                res = {"pid": futs[fut], "ok": False, "error": f"{type(e).__name__}: {e}"}
            print(json.dumps(res, ensure_ascii=False))
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description="Compile + run buggy variants and collect incorrect outputs")
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="Run variants for problems with cache entries")
    r.add_argument("--problems", nargs="*")
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("--workers", type=int, default=4)
    r.add_argument("--timeout", type=float, default=120.0, help="seconds for the binary run")
    r.add_argument("--compile-timeout", type=float, default=120.0)
    r.set_defaults(func=cmd_run)
    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

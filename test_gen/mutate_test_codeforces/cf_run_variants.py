#!/usr/bin/env python3
"""Compile each cache/<pid>/variant_*.rs into a Codeforces ``main.rs`` and run
it once per testcase, recording outputs that disagree with the reference.

Per problem outputs:
    cache/<pid>/incorrect_llm.jsonl   {"input": "...", "output": "<wrong stdout>"}
    cache/<pid>/run.log               compile/run notes

Comparison uses ``normalize_output`` (per-line rstrip + drop trailing blank
lines) to match typical CF judge tolerance, but the *raw* variant stdout is
stored as the wrong output.
"""
from __future__ import annotations

import argparse
import json
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cf_harness_utils import (  # noqa: E402
    CF_DIR,
    assemble_variant_main,
    compile_rust,
    normalize_output,
    run_binary,
)

CACHE_DIR = Path(__file__).resolve().parent / "cache"


def _read_jsonl(path: Path) -> list[dict]:
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def run_one_problem(
    pid: str,
    *,
    timeout: float,
    compile_timeout: float,
) -> dict:
    pdir = CF_DIR / pid
    cache_pdir = CACHE_DIR / pid
    log: list[str] = []
    try:
        main_src = (pdir / "main.rs").read_text()
        testcases = _read_jsonl(pdir / "tests" / "testcases.jsonl")
    except FileNotFoundError as e:
        return {"pid": pid, "ok": False, "error": str(e)}
    if not testcases:
        return {"pid": pid, "ok": False, "error": "empty testcases"}

    variants = sorted(cache_pdir.glob("variant_*.rs"))
    if not variants:
        return {"pid": pid, "ok": False, "error": "no variants in cache"}

    incorrect: list[dict] = []
    seen: set[tuple[str, str]] = set()
    n_compile_fail = 0
    n_run_fail = 0
    n_diff = 0
    n_match = 0
    n_timeout = 0
    n_retained = 0
    n_rejected_all_pass = 0
    n_rejected_all_fail = 0

    with tempfile.TemporaryDirectory(prefix="vcg_cfmut_") as td:
        td_path = Path(td)
        for vp in variants:
            try:
                variant_code = vp.read_text()
                src = assemble_variant_main(main_src, variant_code)
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
            # Stage this variant's results; whether they count depends on the
            # variant's overall pass rate, which we only know after the loop.
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
                key = (tc["input"], stdout)
                v_candidates.append((key, {"input": tc["input"], "output": stdout}))

            n_match += v_match
            n_diff += v_diff

            # Retain only if the pass rate is strictly between 0% and 100%.
            evaluated = v_match + v_diff
            if evaluated == 0:
                log.append(f"{vp.name}: no comparable outputs; dropped")
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
    with open(cache_pdir / "incorrect_llm.jsonl", "w") as f:
        for r in incorrect:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    (cache_pdir / "run.log").write_text("\n".join(log) + "\n")

    return {
        "pid": pid,
        "ok": True,
        "incorrect": len(incorrect),
        "compile_fail": n_compile_fail,
        "run_fail": n_run_fail,
        "timeout": n_timeout,
        "diff": n_diff,
        "match": n_match,
        "variants": len(variants),
        "retained": n_retained,
        "rejected_all_pass": n_rejected_all_pass,
        "rejected_all_fail": n_rejected_all_fail,
    }


def cmd_run(args: argparse.Namespace) -> int:
    if args.problems:
        pids = args.problems
    else:
        pids = sorted(p.name for p in CACHE_DIR.iterdir() if p.is_dir() and p.name.startswith("cf"))
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
    p = argparse.ArgumentParser(description="Run buggy CF variants and collect incorrect outputs")
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--problems", nargs="*")
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("--workers", type=int, default=4)
    r.add_argument("--timeout", type=float, default=10.0, help="seconds per testcase")
    r.add_argument("--compile-timeout", type=float, default=120.0)
    r.set_defaults(func=cmd_run)
    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

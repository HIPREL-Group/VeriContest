#!/usr/bin/env python3
"""Select the VeriContest Lite problems from the current release.

Lite keeps problems that are self-contained, have a unique answer, and whose
reference solution runs with a margin under the time limit. No rule looks at the
proof. Sampling keeps each source and difficulty level at its share of the full
benchmark, and follows the full benchmark's proof sizes: a group's problems are
ranked by proof size and cut into one interval per place, one problem is drawn from
each interval, and a drawn problem that fails a rule is replaced by the eligible
problem closest to it in proof size. The selection is deterministic: the same
release and measurements give the same list.

  measure  time each reference solution on its test cases (writes lite_measurements.jsonl)
  select   apply the criteria and write lite_problem_ids.txt
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import cache
import json
import os
from pathlib import Path
import random
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "evaluation"))
from vceval import checks, harness  # noqa: E402
from vceval.config import LIMITS, VERUS_BIN  # noqa: E402
from vceval.problems import load_checker, load_jsonl, testcase_file  # noqa: E402

SIZE = 300
SEED = "VeriContest Lite 2026-10.1"
MEASUREMENTS = ROOT / "leaderboard/lite_measurements.jsonl"
TIME_MARGIN = 0.5      # share of the per-case limit the reference may use
LINK = re.compile(r"!\[[^\]]*\]\(|<img|https?://", re.I)
DUPLICATE = re.compile(r"\b(?:question|problem) is the same as\b|\b(?:easy|hard) version\b", re.I)


def benchmark(pid):
    return ROOT / "benchmark" / pid


def difficulty(pid):
    tag = (benchmark(pid) / "tags").read_text().splitlines()[0].strip()
    if pid.startswith("leetcode/"):
        return tag
    rating = int(tag.removeprefix("Rating:"))
    for bound, label in ((800, "800"), (1000, "900-1000"), (1200, "1100-1200"), (1400, "1300-1400")):
        if rating <= bound:
            return label
    return "1500+"


@cache
def proof_lines(pid):
    """Lines the reference proof adds to the fixed code and specification."""
    problem = benchmark(pid)
    count = lambda name: sum(1 for ln in (problem / name).read_text().splitlines() if ln.strip())
    return max(0, count("verified.rs") - count("code_spec.rs"))


# -----------------------------------------------------------------------------
# measure
# -----------------------------------------------------------------------------
def _build(pid, program, policy, workdir):
    backend, source = harness.build_source(benchmark(pid), program, policy)
    src, binary = workdir / f"{policy}.rs", workdir / policy
    src.write_text(source)
    if backend == "verus":
        cmd = [str(VERUS_BIN), "--no-verify", "--compile", str(src), "-o", str(binary), "-O"]
    else:
        cmd = [os.environ.get("VCEVAL_RUSTC", "rustc"), "--edition", "2021", "-O", str(src), "-o", str(binary)]
    cp = subprocess.run(cmd, capture_output=True, text=True, timeout=LIMITS["compile_timeout_sec"])
    if cp.returncode != 0:
        raise RuntimeError(f"{pid}: reference does not compile ({policy})\n{cp.stderr[-2000:]}")
    return binary


def time_reference(pid, testcases, repeats=1, only=None):
    """Largest wall-clock time of the reference on one test case, over both builds."""
    mode, _ = harness.template(benchmark(pid))
    checker = load_checker(pid)
    cases = [c for c in load_jsonl(testcase_file(testcases, pid, "testcases.jsonl")) if "output" in c]
    workdir = Path(tempfile.mkdtemp(prefix=pid.replace("/", "_") + "_"))
    times, wrong = {}, 0
    try:
        # verified.rs as a Verus program (End2End, ProofGen), code.rs as plain Rust (CodeGen).
        for file, policy in (("verified.rs", "auto"), ("code.rs", "rustc")):
            binary = _build(pid, (benchmark(pid) / file).read_text(), policy, workdir)
            for i, case in enumerate(cases):
                if only is not None and i not in only:
                    continue
                runs, rp = [], None
                for _ in range(repeats):
                    start = time.perf_counter()
                    try:
                        rp = subprocess.run([str(binary)], input=checks._stdin_for(case, mode),
                                            capture_output=True, text=True, timeout=10 * LIMITS["case_timeout_sec"])
                    except subprocess.TimeoutExpired:
                        runs.append(float("inf"))
                        rp = None
                        continue
                    runs.append(time.perf_counter() - start)
                if repeats == 1 and rp is not None and rp.returncode == 0:
                    row = checks._json_output_line(rp.stdout) if mode == "oracle" else None
                    actual = row["output"] if row is not None and "output" in row else rp.stdout
                    ok = checker(case["input"], actual) if checker else checks._outputs_match(case["output"], actual)
                    wrong += not ok
                times[i] = max(times.get(i, 0.0), statistics.median(runs))
    finally:
        shutil.rmtree(workdir, ignore_errors=True)
    worst = max(times, key=times.get)
    return {"cases": len(cases), "max_case_sec": round(times[worst], 4), "slowest_case": worst,
            "slow_cases": sorted(i for i, t in times.items() if t > TIME_MARGIN * LIMITS["case_timeout_sec"] / 2),
            "wrong_outputs": wrong if only is None else None}


def _timed(args):
    return args[0], time_reference(*args)


def measure(ids, testcases, workers):
    rows = {pid: {"problem_id": pid} for pid in ids}
    with ProcessPoolExecutor(workers) as pool:
        for n, (pid, r) in enumerate(pool.map(_timed, [(p, testcases) for p in ids]), 1):
            rows[pid].update(r)
            print(f"[time {n}/{len(ids)}] {pid} {r['max_case_sec']}s", flush=True)
    # Cases near the margin are timed again, one problem at a time, as the median of
    # three runs, so that load from the parallel pass does not decide the rule.
    for pid in ids:
        if rows[pid]["slow_cases"]:
            again = time_reference(pid, testcases, repeats=3, only=set(rows[pid]["slow_cases"]))
            rows[pid]["max_case_sec_serial"] = again["max_case_sec"]
            print(f"[retime] {pid} {rows[pid]['max_case_sec']}s -> {again['max_case_sec']}s", flush=True)
    return [rows[pid] for pid in ids]


# -----------------------------------------------------------------------------
# select
# -----------------------------------------------------------------------------
def exclusion(pid, measured):
    """Return why a problem is left out of Lite, or None if it is a candidate."""
    problem = benchmark(pid)
    description = (problem / "description.md").read_text()
    if LINK.search(description):
        return "description has an image or a hyperlink"
    if DUPLICATE.search(description):
        return "description refers to another problem"
    if (problem / "tests" / "checker.py").exists():
        return "outputs are judged by a checker"
    m = measured[pid]
    if m.get("max_case_sec_serial", m["max_case_sec"]) > TIME_MARGIN * LIMITS["case_timeout_sec"]:
        return f"reference uses more than {TIME_MARGIN:.0%} of the per-case time limit"
    return None


def quotas(strata, size):
    """Split size over the strata in proportion to their full-benchmark counts."""
    total = sum(strata.values())
    exact = {key: size * count / total for key, count in strata.items()}
    share = {key: int(value) for key, value in exact.items()}
    for key in sorted(exact, key=lambda k: (share[k] - exact[k], k))[:size - sum(share.values())]:
        share[key] += 1
    return share


def draw(ids, eligible, size, seed):
    rng = random.Random(seed)
    group = {pid: (pid.split("/")[0], difficulty(pid)) for pid in ids}
    chosen = set()
    for source, n in sorted(quotas(Counter(g[0] for g in group.values()), size).items()):
        for g, k in sorted(quotas(Counter(v for v in group.values() if v[0] == source), n).items()):
            members = sorted((p for p in ids if group[p] == g), key=lambda p: (proof_lines(p), p))
            for i in range(k):
                pick = members[rng.randrange(len(members) * i // k, len(members) * (i + 1) // k)]
                pool = [p for p in members if p in eligible and p not in chosen]
                if not pool:
                    raise ValueError(f"group {g} has too few eligible problems")
                chosen.add(min(pool, key=lambda p: (abs(proof_lines(p) - proof_lines(pick)), p != pick, p)))
    return [p for p in ids if p in chosen]


def select(ids, measured):
    missing = [p for p in ids if p not in measured]
    if missing:
        raise ValueError(f"{len(missing)} problems have no measurements, e.g. {missing[0]}; run measure")
    reasons = {pid: exclusion(pid, measured) for pid in ids}
    eligible = {p for p in ids if reasons[p] is None}
    return draw(ids, eligible, SIZE, SEED), reasons


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    p = commands.add_parser("measure", help="time and re-verify every reference solution")
    p.add_argument("--testcases", type=Path, default=os.environ.get("VERICONTEST_TESTCASES"),
                   help="test-case dataset (<family>/<problem>/tests/testcases.jsonl)")
    p.add_argument("--workers", type=int, default=24)
    p.add_argument("--problems", help="comma-separated subset (debugging only)")
    p = commands.add_parser("select", help="apply the criteria and write the Lite list")
    p.add_argument("--output-dir", type=Path, default=ROOT / "leaderboard")
    args = parser.parse_args()
    ids = (ROOT / "leaderboard/problem_ids.txt").read_text().split()
    if args.command == "measure":
        if args.testcases is None:
            parser.error("measure needs --testcases or VERICONTEST_TESTCASES")
        rows = measure(args.problems.split(",") if args.problems else ids, args.testcases, args.workers)
        MEASUREMENTS.write_text("".join(json.dumps(r) + "\n" for r in rows))
        print(f"Wrote {len(rows)} measurements to {MEASUREMENTS}")
        return 0
    measured = {r["problem_id"]: r for r in load_jsonl(MEASUREMENTS)}
    lite, reasons = select(ids, measured)
    (args.output_dir / "lite_problem_ids.txt").write_text("".join(p + "\n" for p in lite))
    for reason, n in Counter(r for r in reasons.values() if r).most_common():
        print(f"excluded {n:4d}: {reason}")
    print(f"candidates {sum(r is None for r in reasons.values())} of {len(ids)}")
    for key, n in sorted(Counter((p.split("/")[0], difficulty(p)) for p in lite).items()):
        print(f"  {' '.join(key):24s} {n:3d}")
    print(f"Wrote {len(lite)} Lite problems to {args.output_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

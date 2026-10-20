"""Official VeriContest scorer.

Input: one final program per problem, ``<outputs>/<family>/<problem>.rs``.
Output: ``results.jsonl`` in the leaderboard record format, one JSON log per
problem under ``eval_logs/``, and ``summary.json``.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import traceback
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from . import checks, spec_tests
from .config import CHECK_KEYS, LIMITS, REPO_ROOT, TASKS, VERUS_BIN, VERUS_FLAGS, release_info
from .problems import SPLITS, all_problem_ids, problem_dir, select


def score_one(task_key: tuple[str, str], problem_id: str, program: str | None,
              testcases: Path, lynette: str | None, tmp_root: Path) -> dict:
    """Run the task's checks on one problem's program."""
    spec = TASKS[task_key]
    result = {k: ({"status": "not_run"} if k in spec["checks"] else {"status": "not_applicable"})
              for k in CHECK_KEYS}
    if program is None:
        return result
    workdir = Path(tempfile.mkdtemp(prefix=problem_id.replace("/", "_") + "_", dir=tmp_root))
    task = task_key[0]
    try:
        if task == "SpecGen":
            # Typecheck, then test the specification on the test cases with
            # post2exe; what post2exe cannot test is left to human review.
            typed = checks.typecheck_spec(program, workdir)
            result["spec_tests"] = (spec_tests.spec_tests(problem_id, program, testcases, workdir)
                                    if typed["status"] == "pass" else typed)
        elif task == "CodeGen":
            result["code_tests"] = checks.code_tests(problem_id, program, spec["compile"], testcases, workdir)
        elif task == "ProofGen":
            if lynette is None:
                result["verus"] = {"status": "error", "log": "lynette not found; run evaluation/setup_tools.sh"}
            else:
                kept = checks.preserved((problem_dir(problem_id) / "code_spec.rs").read_text(),
                                        program, workdir, lynette)
                result["verus"] = checks.verify(program, workdir) if kept["status"] == "pass" else kept
        elif task == "End2End":
            # Verify first; test cases run only for verified programs, and the
            # specification is tested only when both pass.
            result["verus"] = checks.verify(program, workdir)
            if result["verus"]["status"] == "pass":
                result["code_tests"] = checks.code_tests(problem_id, program, spec["compile"], testcases, workdir)
            if result["code_tests"]["status"] == "pass":
                result["spec_tests"] = spec_tests.spec_tests(problem_id, program, testcases, workdir)
    except Exception:
        for k in spec["checks"]:
            if result[k]["status"] == "not_run":
                result[k] = {"status": "error", "log": traceback.format_exc()[-3000:]}
    finally:
        shutil.rmtree(workdir, ignore_errors=True)
    return result


def automatic_pass(task: str, result: dict) -> bool:
    """Every automatic check passes, including the post2exe specification test."""
    return all(result[k]["status"] == "pass" for k in TASKS_BY_TASK[task])


def needs_spec_review(task: str, result: dict) -> bool:
    """Every other check passes, but post2exe could not test the specification
    (``spec_tests`` is ``unsupported``): the verdict needs human review."""
    others = [k for k in TASKS_BY_TASK[task] if k != "spec_tests"]
    return (result.get("spec_tests", {}).get("status") == "unsupported"
            and all(result[k]["status"] == "pass" for k in others))


TASKS_BY_TASK = {task: spec["checks"] for (task, _), spec in TASKS.items()}


def _note(task: str, status: str, result: dict) -> str:
    if status != "produced":
        return f"No program ({status})."
    parts = []
    for k in TASKS_BY_TASK[task]:
        r = result[k]
        detail = f" {r['passed']}/{r['total']}" if "passed" in r else ""
        if r.get("review_reason"):
            detail += f" (human review: {r['review_reason']})"
        elif k == "spec_tests" and r["status"] == "fail" and r.get("log"):
            detail += f" ({r['log'][:200]})"
        parts.append(f"{k}={r['status']}{detail}")
    return "; ".join(parts) + "."


def _version(cmd: list[str]) -> str | None:
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=60).stdout.strip() or None
    except (OSError, subprocess.TimeoutExpired):
        return None


def environment() -> dict:
    rev = _version(["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"])
    if rev:
        dirty = bool(_version(["git", "-C", str(REPO_ROOT), "status", "--porcelain", "--", "evaluation", "post2exe"]))
    else:  # Docker image: revision baked in at build time
        rev, dirty = os.environ.get("VCEVAL_REVISION") or None, None
    return {
        "evaluator_revision": rev, "evaluator_dirty": dirty, **release_info(),
        "verus_flags": VERUS_FLAGS,
        "verus": _version([str(VERUS_BIN), "--version"]),
        "rustc": _version([os.environ.get("VCEVAL_RUSTC", "rustc"), "--version"]),
        "python": sys.version.split()[0], "limits": LIMITS,
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--task", required=True, choices=sorted({t for t, _ in TASKS}))
    ap.add_argument("--input-mode", required=True)
    ap.add_argument("--outputs", required=True, type=Path, help="directory with <family>/<problem>.rs")
    ap.add_argument("--testcases", type=Path, default=os.environ.get("VERICONTEST_TESTCASES"),
                    help="local copy of the Hugging Face dataset (<family>/<problem>/tests/*.jsonl)")
    ap.add_argument("--out", required=True, type=Path, help="directory for results.jsonl, eval_logs/, summary.json")
    ap.add_argument("--split", default="full", choices=SPLITS)
    ap.add_argument("--problems", help="comma-separated subset (debugging only; not a valid submission)")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--artifact-prefix", default="programs/",
                    help="bundle path prefix recorded in results.jsonl artifacts.program")
    ap.add_argument("--tmp", type=Path, default=None, help="scratch directory (default: system temp)")
    args = ap.parse_args(argv)

    key = (args.task, args.input_mode)
    if key not in TASKS:
        ap.error(f"invalid task/input mode {key}; valid: {sorted(TASKS)}")
    needs_tests = args.task in {"CodeGen", "End2End"}
    if needs_tests and (args.testcases is None or not Path(args.testcases).is_dir()):
        ap.error("--testcases (or VERICONTEST_TESTCASES) must point to the downloaded test cases")
    lynette = checks.lynette_path()
    if args.task == "ProofGen" and lynette is None:
        ap.error("ProofGen needs lynette: run evaluation/setup_tools.sh or set VCEVAL_LYNETTE")

    ids = select(all_problem_ids(), args.problems, args.split)
    generation = {}
    manifest = args.outputs / "generation.jsonl"
    if manifest.is_file():
        for line in manifest.read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                generation[row["problem_id"]] = row["generation_status"]

    args.out.mkdir(parents=True, exist_ok=True)
    tmp_root = Path(tempfile.mkdtemp(prefix="vceval_", dir=args.tmp))
    started = time.time()
    results: dict[str, dict] = {}
    statuses: dict[str, str] = {}
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {}
        for pid in ids:
            path = args.outputs / f"{pid}.rs"
            program = path.read_text() if path.is_file() else None
            statuses[pid] = generation.get(pid, "produced" if program is not None else "not_attempted")
            if statuses[pid] != "produced":
                program = None
            futures[pool.submit(score_one, key, pid, program, Path(args.testcases or "."), lynette, tmp_root)] = pid
        for n, fut in enumerate(as_completed(futures), 1):
            pid = futures[fut]
            results[pid] = fut.result()
            produced = statuses[pid] == "produced"
            verdict = ("PASS" if produced and automatic_pass(args.task, results[pid]) else
                       "REVIEW" if produced and needs_spec_review(args.task, results[pid]) else "fail")
            print(f"[{n}/{len(ids)}] {pid}: {verdict}  "
                  f"{_note(args.task, statuses[pid], results[pid])}", flush=True)
    shutil.rmtree(tmp_root, ignore_errors=True)

    rows, passed, review = [], [], {}
    for pid in ids:
        res, status = results[pid], statuses[pid]
        log_rel = f"eval_logs/{pid}.json"
        (args.out / log_rel).parent.mkdir(parents=True, exist_ok=True)
        (args.out / log_rel).write_text(json.dumps({"problem_id": pid, "generation_status": status,
                                                    "checks": res}, indent=2, default=str) + "\n")
        rows.append({"problem_id": pid, "run_id": "run-1", "attempt_id": "1", "generation_status": status,
                     "artifacts": {"program": f"{args.artifact_prefix}{pid}.rs"} if status == "produced" else {},
                     "checks": {k: res[k]["status"] for k in CHECK_KEYS},
                     "logs": {"evaluation": log_rel}, "notes": _note(args.task, status, res)})
        if status == "produced" and automatic_pass(args.task, res):
            passed.append(pid)
        elif status == "produced" and needs_spec_review(args.task, res):
            review[pid] = res["spec_tests"].get("review_reason", "")
    (args.out / "results.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))

    counts = {k: {} for k in CHECK_KEYS}
    for r in rows:
        for k, v in r["checks"].items():
            counts[k][v] = counts[k].get(v, 0) + 1
    summary = {
        "task": args.task, "input_mode": args.input_mode, "split": args.split,
        "subset": bool(args.problems), "problems": len(ids),
        "automatic_pass": len(passed), "automatic_pass_at_1": 100 * len(passed) / len(ids) if ids else 0.0,
        "needs_human_spec_review": bool(review),
        "check_counts": counts, "passed_problem_ids": passed,
        # Every other check passed, but post2exe could not test the specification.
        "spec_review_problem_ids": review,
        "wall_time_sec": round(time.time() - started, 1), "environment": environment(),
    }
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"\n{args.task}/{args.input_mode}: automatic pass {len(passed)}/{len(ids)} "
          f"({summary['automatic_pass_at_1']:.1f}%)")
    if review:
        print(f"{len(review)} more problems pass every other check but need human specification "
              "review (post2exe could not test them); see spec_review_problem_ids in summary.json.")
    print(f"Wrote {args.out}/results.jsonl, eval_logs/, summary.json")


if __name__ == "__main__":
    main()

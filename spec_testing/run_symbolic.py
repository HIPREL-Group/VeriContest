"""Symbolic test CLI (single problem): generate/reuse the test store, decide
every case with Verus probes, write results to the problem's results dir.

  python -m spec_testing.run_symbolic lc121            # skip if results present
  python -m spec_testing.run_symbolic lc121 --force    # regenerate everything

Exit codes: 0 ran or skipped with no findings, 1 findings (REJECTED positive
or confirmed ACCEPTED negative), 2 problem not found, 3 crash / unsupported.
"""
from __future__ import annotations

import argparse
import sys
import traceback
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from spec_testing import symbolic  # noqa: E402
from spec_testing.common import cli, layout  # noqa: E402

OWNED_FILES = ("pos_tests", "neg_tests", "symbolic_pos", "symbolic_neg")


def results_present(problem) -> bool:
    return (layout.path(problem.kind, problem.problem_id, "symbolic_pos").exists()
            and layout.path(problem.kind, problem.problem_id, "symbolic_neg").exists())


def clear_owned(problem) -> None:
    """--force: delete only the symbolic-owned files, never sanity_vacuity.json."""
    for name in OWNED_FILES:
        layout.path(problem.kind, problem.problem_id, name).unlink(missing_ok=True)


def _fmt_counts(counts: dict) -> str:
    return "/".join(str(counts.get(k, 0)) for k in ("ACCEPTED", "REJECTED", "UNDECIDED"))


def report_lines(pid: str, detail: dict) -> list[str]:
    if "unsupported" in detail:
        return [f"[{pid}] symbolic: unsupported ({detail['unsupported']})"]
    if "skipped" in detail:
        return [f"[{pid}] symbolic: no positive cases -> skipped"]
    lines = [f"[{pid}] symbolic: cases pos={detail.get('n_pos')} "
             f"neg={detail.get('n_neg')} ({detail.get('cases')})",
             f"[{pid}] pos A/R/U = {_fmt_counts(detail.get('pos', {}))}   "
             f"neg A/R/U = {_fmt_counts(detail.get('neg', {}))}   "
             f"harness_health={detail.get('harness_health')}"]
    for f in detail.get("findings", []):
        lines.append(f"  FINDING {f['kind']}: {f['case_id']}")
    return lines


def run_one(problem, force: bool) -> dict:
    if force:
        clear_owned(problem)
    return symbolic.run(problem, force=force)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("problem_id")
    ap.add_argument("--kind", default=None, choices=list(cli.KIND_ORDER))
    ap.add_argument("--force", action="store_true",
                    help="redo even when results exist (regenerates the test store)")
    args = ap.parse_args()

    problem = cli.resolve(args.problem_id, args.kind)
    if not args.force and results_present(problem):
        print(f"[{problem.problem_id}] symbolic: skip (results present; --force to redo)")
        return 0
    try:
        detail = run_one(problem, args.force)
    except Exception:
        traceback.print_exc()
        return 3
    print("\n".join(report_lines(problem.problem_id, detail)))
    if "unsupported" in detail:
        return 3
    if "skipped" in detail:
        return 0
    print(f"[{problem.problem_id}] findings={len(detail.get('findings', []))} "
          f"-> {layout.problem_dir(problem.kind, problem.problem_id)}")
    return 1 if detail.get("findings") else 0


if __name__ == "__main__":
    raise SystemExit(main())

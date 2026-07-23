"""Sanity-vacuity-check CLI (single problem).

  python -m spec_testing.run_sanity lc121            # console report only
  python -m spec_testing.run_sanity lc121 --save     # also write sanity_vacuity.json

Exit codes: 0 clean, 1 flags present / vacuity not run / unsupported spec,
2 problem not found, 3 crash.
"""
from __future__ import annotations

import argparse
import sys
import traceback
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from spec_testing import sanity  # noqa: E402
from spec_testing.common import cli, layout  # noqa: E402


def report_lines(pid: str, report: dict) -> tuple[list[str], bool]:
    """Console lines + flagged?  for one sanity report."""
    if "unsupported" in report:
        return [f"[{pid}] sanity: unsupported ({report['unsupported']})"], True
    flags = report.get("flags", [])
    sp = report.get("seed_pre", {})
    sp_txt = ("skip" if str(sp.get("status", "")).startswith("skip")
              else (f"refuted:{sp['refuted']}" if sp.get("refuted") else "ok"))
    head = (f"[{pid}] sanity: {len(flags)} flag(s)" if flags
            else f"[{pid}] sanity: clean")
    lines = [head]
    for f in flags:
        probe = f.get("probe") or f.get("check", "?")
        lines.append(f"  {f.get('severity', '?')} {probe}: {f.get('message', '')}")
    lines.append(f"  vacuity={report.get('vacuity_status')} seed_pre={sp_txt}")
    flagged = bool(flags) or bool(sp.get("refuted"))
    return lines, flagged


def run_one(problem, save: bool) -> tuple[dict, bool]:
    report = sanity.run(problem)
    if save:
        layout.write_json(
            layout.path(problem.kind, problem.problem_id, "sanity_vacuity"), report)
    _, flagged = report_lines(problem.problem_id, report)
    return report, flagged


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("problem_id")
    ap.add_argument("--kind", default=None, choices=list(cli.KIND_ORDER))
    ap.add_argument("--save", action="store_true",
                    help="write the report to results/<kind>/<pid>/sanity_vacuity.json")
    args = ap.parse_args()

    problem = cli.resolve(args.problem_id, args.kind)
    try:
        report, flagged = run_one(problem, args.save)
    except Exception:
        traceback.print_exc()
        return 3
    lines, _ = report_lines(problem.problem_id, report)
    print("\n".join(lines))
    if args.save:
        print(f"saved -> {layout.path(problem.kind, problem.problem_id, 'sanity_vacuity')}")
    return 1 if flagged else 0


if __name__ == "__main__":
    raise SystemExit(main())

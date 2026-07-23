"""Sanity-vacuity-check CLI (batch).

  python -m spec_testing.run_sanity_batch [--kind leetcode] [--problems lc121,lc134]
                                          [--limit N] [--save]

Prints one status line per problem (flag details follow flagged ones); --save
also writes every report to results/<kind>/<pid>/sanity_vacuity.json. Exit
codes: 0 ran (flags allowed), 1 at least one per-problem error, 2 bad args.
"""
from __future__ import annotations

import argparse
import sys
import traceback
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from spec_testing.common import cli  # noqa: E402
from spec_testing.run_sanity import run_one  # noqa: E402


def _status_line(pid: str, report: dict, flagged: bool) -> str:
    if "unsupported" in report:
        return f"[{pid}] unsupported ({report['unsupported']})"
    sp = report.get("seed_pre", {})
    sp_txt = ("skip" if str(sp.get("status", "")).startswith("skip")
              else (f"refuted:{sp['refuted']}" if sp.get("refuted") else "ok"))
    tag = f"FLAGGED({len(report.get('flags', []))})" if flagged else "clean"
    return (f"[{pid}] {tag}  vacuity={report.get('vacuity_status')} seed_pre={sp_txt}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    cli.add_batch_args(ap)
    ap.add_argument("--save", action="store_true")
    args = ap.parse_args()

    tally: dict[str, dict[str, int]] = {}
    errors = 0
    for p in cli.select(args.kind, args.problems, args.limit):
        t = tally.setdefault(p.kind, {"run": 0, "clean": 0, "flagged": 0, "errors": 0})
        t["run"] += 1
        try:
            report, flagged = run_one(p, args.save)
        except KeyboardInterrupt:
            raise
        except Exception:
            t["errors"] += 1
            errors += 1
            print(f"[{p.problem_id}] ERROR\n{traceback.format_exc()}",
                  file=sys.stderr, flush=True)
            continue
        # one heartbeat line per problem, flushed so it shows live even when
        # stdout is redirected to a file
        print(_status_line(p.problem_id, report, flagged), flush=True)
        if flagged:
            t["flagged"] += 1
            for f in report.get("flags", []):
                probe = f.get("probe") or f.get("check", "?")
                print(f"    {f.get('severity', '?')} {probe}: {f.get('message', '')}",
                      flush=True)
        else:
            t["clean"] += 1

    rows = [[k, t["run"], t["clean"], t["flagged"], t["errors"]]
            for k, t in tally.items()]
    if len(rows) > 1:
        rows.append(["total", *[sum(r[i] for r in rows) for i in range(1, 5)]])
    print()
    print(cli.table(["kind", "run", "clean", "flagged", "errors"], rows))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())

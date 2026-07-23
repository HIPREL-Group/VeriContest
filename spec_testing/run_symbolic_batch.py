"""Symbolic test CLI (batch).

  python -m spec_testing.run_symbolic_batch [--kind all] [--problems lc121,lc134]
                                            [--limit N] [--force]

Problems whose symbolic_pos.json + symbolic_neg.json already exist are
skipped (--force redoes them). Exit codes: 0 no errors, 1 at least one
per-problem error, 2 bad args.
"""
from __future__ import annotations

import argparse
import json
import sys
import traceback
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from spec_testing.common import cli  # noqa: E402
from spec_testing.run_symbolic import (  # noqa: E402
    _fmt_counts, results_present, run_one)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    cli.add_batch_args(ap)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--summary", metavar="PATH", default=None,
                    help="write a machine-readable per-problem summary JSON")
    args = ap.parse_args()

    rows: list[list[str]] = []
    summary: list[dict] = []
    tally = {"ok": 0, "skipped": 0, "error": 0, "findings": 0}
    for p in cli.select(args.kind, args.problems, args.limit):
        pid = p.problem_id
        if not args.force and results_present(p):
            tally["skipped"] += 1
            summary.append({"pid": pid, "kind": p.kind, "status": "skipped"})
            print(f"[batch] {pid}: skip (cached)", flush=True)
            continue
        # heartbeat before the expensive work so the current problem is visible
        print(f"[batch] {pid}: running...", flush=True)
        try:
            detail = run_one(p, args.force)
        except KeyboardInterrupt:
            raise
        except Exception:
            tally["error"] += 1
            rows.append([pid, "error", "-", "-", "crash"])
            summary.append({"pid": pid, "kind": p.kind, "status": "error"})
            print(f"[batch] {pid}: ERROR\n{traceback.format_exc()}",
                  file=sys.stderr, flush=True)
            continue
        if "unsupported" in detail:
            tally["error"] += 1
            rows.append([pid, "error", "-", "-", detail["unsupported"]])
            summary.append({"pid": pid, "kind": p.kind, "status": "unsupported",
                            "reason": detail["unsupported"]})
            print(f"[batch] {pid}: unsupported ({detail['unsupported']})", flush=True)
            continue
        if "skipped" in detail:
            tally["skipped"] += 1
            rows.append([pid, "empty", "-", "-", "no positives"])
            summary.append({"pid": pid, "kind": p.kind, "status": "empty",
                            "reason": detail["skipped"]})
            print(f"[batch] {pid}: no positive cases -> skipped", flush=True)
            continue
        n_findings = len(detail.get("findings", []))
        tally["ok"] += 1
        tally["findings"] += n_findings
        pos, neg = _fmt_counts(detail.get("pos", {})), _fmt_counts(detail.get("neg", {}))
        rows.append([pid, "ok", pos, neg, n_findings])
        summary.append({"pid": pid, "kind": p.kind, "status": "ok",
                        "pos": detail.get("pos", {}), "neg": detail.get("neg", {}),
                        "harness_health": detail.get("harness_health"),
                        "findings": detail.get("findings", []),
                        "wall_s": detail.get("wall_s")})
        print(f"[batch] {pid}: ok pos {pos} neg {neg} findings={n_findings}", flush=True)

    if rows:
        print()
        print(cli.table(["pid", "status", "pos A/R/U", "neg A/R/U", "findings"], rows))
    print(f"\n[batch] done: ok={tally['ok']} skipped={tally['skipped']} "
          f"error={tally['error']} findings={tally['findings']}")
    if args.summary:
        Path(args.summary).write_text(
            json.dumps({"tally": tally, "problems": summary}, indent=1),
            encoding="utf-8")
        print(f"summary -> {args.summary}")
    return 1 if tally["error"] else 0


if __name__ == "__main__":
    raise SystemExit(main())

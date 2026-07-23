"""Shared helpers for the four spec_testing CLI entry points."""
from __future__ import annotations

import sys

from spec_testing.common import repo

KIND_ORDER = ("leetcode", "codeforces", "extended")


def resolve(problem_id: str, kind: str | None) -> repo.Problem:
    p = repo.find(problem_id, kind)
    if p is None:
        print(f"problem '{problem_id}' not found", file=sys.stderr)
        raise SystemExit(2)
    return p


def add_batch_args(ap) -> None:
    ap.add_argument("--kind", default="all", choices=["all", *KIND_ORDER])
    ap.add_argument("--problems", default="all",
                    help="comma-separated problem ids, or 'all'")
    ap.add_argument("--limit", type=int, default=0)


def select(kind: str, problems: str, limit: int) -> list[repo.Problem]:
    kinds = KIND_ORDER if kind == "all" else (kind,)
    probs: list[repo.Problem] = []
    for k in kinds:
        probs.extend(repo.discover((k,)))
    if problems != "all":
        ids = set(problems.split(","))
        probs = [p for p in probs if p.problem_id in ids]
    if limit:
        probs = probs[:limit]
    return probs


def table(headers: list[str], rows: list[list[str]]) -> str:
    widths = [max(len(str(headers[i])), *(len(str(r[i])) for r in rows)) if rows
              else len(str(headers[i])) for i in range(len(headers))]
    fmt = "  ".join(f"{{:<{w}}}" for w in widths)
    lines = [fmt.format(*headers)]
    lines += [fmt.format(*[str(c) for c in r]) for r in rows]
    return "\n".join(lines)

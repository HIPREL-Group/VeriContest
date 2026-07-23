"""Problem discovery and file loading.

A "problem" is a directory under benchmark/{leetcode,codeforces,extended}/ that
holds spec.rs / code.rs / verified.rs / description.md (+ main.rs for CF).
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .config import REPO_ROOT

BENCHMARK_DIR = REPO_ROOT / "benchmark"
KINDS = ("leetcode", "codeforces", "extended")


@dataclass(frozen=True)
class Problem:
    problem_id: str            # e.g. "lc1004", "cf1006C"
    kind: str                  # "leetcode" | "codeforces" | "extended"
    dir: Path

    @property
    def is_codeforces(self) -> bool:
        return self.kind == "codeforces"

    def read(self, name: str) -> str | None:
        p = self.dir / name
        if not p.exists():
            return None
        return p.read_text(encoding="utf-8")


def _looks_like_problem(d: Path) -> bool:
    return (d / "spec.rs").exists()


def discover(kinds: tuple[str, ...] = KINDS) -> list[Problem]:
    """Return all problems under the requested benchmark kinds, sorted by id."""
    out: list[Problem] = []
    for kind in kinds:
        base = BENCHMARK_DIR / kind
        if not base.is_dir():
            continue
        for d in sorted(base.iterdir()):
            if d.is_dir() and _looks_like_problem(d):
                out.append(Problem(problem_id=d.name, kind=kind, dir=d))
    return out


def find(problem_id: str, kind: str | None = None) -> Problem | None:
    for p in discover(KINDS if kind is None else (kind,)):
        if p.problem_id == problem_id:
            return p
    return None

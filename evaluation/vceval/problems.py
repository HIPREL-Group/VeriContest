"""Benchmark problem discovery and testcase loading."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path

from .config import BENCH_ROOT, FAMILIES, REPO_ROOT


def all_problem_ids() -> list[str]:
    """Problem IDs of the current release, e.g. ``leetcode/lc1``."""
    listed = REPO_ROOT / "leaderboard" / "problem_ids.txt"
    if listed.is_file():
        return [line.strip() for line in listed.read_text().splitlines() if line.strip()]
    return [f"{family}/{d.name}" for family in FAMILIES
            for d in sorted((BENCH_ROOT / family).iterdir()) if d.is_dir()]


def problem_dir(problem_id: str) -> Path:
    return BENCH_ROOT / problem_id


# Lite is a fixed list of the release (leaderboard/LITE.md).
SPLIT_LISTS = {"lite": "lite_problem_ids.txt"}
SPLITS = ("full", *FAMILIES, *SPLIT_LISTS)


def select(ids: list[str], problems: str | None, split: str) -> list[str]:
    if split in SPLIT_LISTS:
        listed = (REPO_ROOT / "leaderboard" / SPLIT_LISTS[split]).read_text().split()
        ids = [p for p in ids if p in set(listed)]
    elif split != "full":
        ids = [p for p in ids if p.startswith(split + "/")]
    if problems:
        wanted = {p.strip() for p in problems.split(",") if p.strip()}
        # Accept bare names such as lc1 as well as leetcode/lc1.
        ids = [p for p in ids if p in wanted or p.split("/")[1] in wanted]
    return ids


def testcase_file(testcases_root: Path, problem_id: str, name: str) -> Path:
    """Path of ``testcases.jsonl`` / ``mutated_testcases.jsonl`` in the dataset."""
    return testcases_root / problem_id / "tests" / name


def load_jsonl(path: Path) -> list[dict]:
    rows = []
    with path.open() as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def load_checker(problem_id: str):
    """The problem's ``check(input, output)`` function, or None."""
    path = problem_dir(problem_id) / "tests" / "checker.py"
    if not path.is_file():
        return None
    spec = importlib.util.spec_from_file_location(f"checker_{problem_id.replace('/', '_')}", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.check

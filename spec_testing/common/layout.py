"""Per-problem output layout. Everything a problem produces lives in one
committed directory:

spec_testing/results/<kind>/<pid>/
    sanity_vacuity.json   # sanity-vacuity-check report
    pos_tests.json        # final proved+deduped positive cases (seeds first)
    neg_tests.json        # final deduped negative cases (exec_mut, outmut, cross)
    symbolic_pos.json     # per-case verdicts on positives
    symbolic_neg.json     # per-case verdicts on negatives
"""
from __future__ import annotations

import json
from pathlib import Path

from spec_testing.common.config import SPEC_TESTING_DIR

PROBLEMS_ROOT = SPEC_TESTING_DIR / "results"

FILES = {
    "sanity_vacuity": "sanity_vacuity.json",
    "pos_tests": "pos_tests.json",
    "neg_tests": "neg_tests.json",
    "symbolic_pos": "symbolic_pos.json",
    "symbolic_neg": "symbolic_neg.json",
}


def problem_dir(kind: str, problem_id: str) -> Path:
    return PROBLEMS_ROOT / kind / problem_id


def path(kind: str, problem_id: str, name: str) -> Path:
    return problem_dir(kind, problem_id) / FILES[name]


def _dump_row(v) -> str:
    return json.dumps(v, ensure_ascii=False, default=str)


def _render(obj, depth: int = 0) -> str:
    """Readable JSON: one line per row. Lists of composites put each element
    on its own (compact) line; dicts get one line per key, recursing one
    level so nested sections stay browsable."""
    pad = " " * depth
    if isinstance(obj, list) and obj and any(isinstance(e, (dict, list)) for e in obj):
        rows = ",\n".join(pad + " " + _dump_row(e) for e in obj)
        return "[\n" + rows + "\n" + pad + "]"
    if isinstance(obj, dict) and depth < 2:
        if not obj:
            return "{}"
        parts = []
        for k, v in obj.items():
            parts.append(f'{pad} {json.dumps(str(k))}: {_render(v, depth + 1)}')
        return "{\n" + ",\n".join(parts) + "\n" + pad + "}"
    return _dump_row(obj)


def write_json(p: Path, obj) -> None:
    """Atomic write: tmp file then rename."""
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(p.suffix + ".tmp")
    tmp.write_text(_render(obj) + "\n", encoding="utf-8")
    tmp.replace(p)


def read_json(p: Path, default=None):
    if not p.exists():
        return default
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return default


def load_cases(kind: str, problem_id: str, name: str) -> list[dict]:
    """Load case rows from a case file (plain list or {"rows": [...]} wrapper)."""
    rows = read_json(path(kind, problem_id, name), default=[])
    if isinstance(rows, dict):
        rows = rows.get("rows", [])
    return rows

"""Helpers for assembling, compiling and running variant LeetCode harnesses.

A variant is just the body of ``code.rs`` (e.g. one or more ``impl`` blocks plus
optional helper structs). We splice it into the original ``harness.rs`` between
the ``pub struct Solution;`` declaration and the ``use std::io::...`` line that
starts the harness boilerplate.
"""
from __future__ import annotations

import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
LEETCODE_DIR = REPO_ROOT / "benchmark" / "leetcode"

MUTATED_TESTCASES_NAME = "mutated_testcases.jsonl"

HARNESS_SPLIT_MARKER = "use std::io::{self, BufRead, Write, BufWriter};"


def mutated_testcases_path(pdir: Path) -> Path:
    """Path to the per-problem mutated testcase JSONL (may be absent)."""
    return pdir / "tests" / MUTATED_TESTCASES_NAME


def has_mutated_testcases(pdir: Path) -> bool:
    """True if this problem already has a ``mutated_testcases.jsonl`` file."""
    return mutated_testcases_path(pdir).is_file()


@dataclass
class HarnessParts:
    pre_marker: str
    post_marker: str  # includes the marker line


def split_harness(harness_src: str) -> HarnessParts:
    idx = harness_src.find(HARNESS_SPLIT_MARKER)
    if idx == -1:
        raise ValueError("harness.rs missing expected split marker")
    return HarnessParts(
        pre_marker=harness_src[:idx],
        post_marker=harness_src[idx:],
    )


def assemble_variant_source(harness_src: str, variant_code: str) -> str:
    """Return a full Rust source file with ``variant_code`` spliced into the harness."""
    parts = split_harness(harness_src)
    # ``pub struct Solution;`` already lives inside pre_marker (it's the first line).
    # We replace everything *after* it (the original impl block) with the variant.
    pre = parts.pre_marker
    m = re.search(r"pub\s+struct\s+Solution\s*;\s*\n", pre)
    if not m:
        raise ValueError("harness.rs missing 'pub struct Solution;' declaration")
    head = pre[: m.end()]
    return f"{head}\n{variant_code.strip()}\n\n{parts.post_marker}"


def compile_rust(src_path: Path, bin_path: Path, *, timeout: float = 60.0) -> tuple[bool, str]:
    cmd = [
        "rustc",
        "--edition",
        "2021",
        "-O",
        "-A",
        "warnings",
        str(src_path),
        "-o",
        str(bin_path),
    ]
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as e:
        return False, f"rustc timeout ({timeout}s): {e}"
    ok = proc.returncode == 0
    return ok, proc.stderr or proc.stdout


def run_binary_with_inputs(
    bin_path: Path,
    input_lines: list[str],
    *,
    timeout: float = 60.0,
) -> tuple[bool, list[str], str]:
    """Run the compiled binary; feed each input line on stdin, capture stdout lines."""
    stdin = "\n".join(input_lines) + "\n"
    try:
        proc = subprocess.run(
            [str(bin_path)],
            input=stdin,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False, [], "binary timed out"
    stdout_lines = [line for line in proc.stdout.splitlines() if line.strip()]
    return proc.returncode == 0, stdout_lines, proc.stderr


def parse_output_field(line: str):
    """Parse one harness output line and return its ``output`` value, or None on failure."""
    line = line.strip()
    if not line.startswith("{") or not line.endswith("}"):
        return None
    try:
        obj = json.loads(line)
    except json.JSONDecodeError:
        return None
    if isinstance(obj, dict) and "output" in obj:
        return obj["output"]
    return None


def load_problem_files(problem_dir: Path) -> tuple[str, str, str]:
    """Return (description.md text, code.rs text, harness.rs text) for a problem."""
    desc = (problem_dir / "description.md").read_text()
    code = (problem_dir / "code.rs").read_text()
    harness = (problem_dir / "tests" / "harness.rs").read_text()
    return desc, code, harness


def list_leetcode_problems(*, only_missing_mutated: bool = True) -> list[Path]:
    """List LeetCode problem dirs under ``benchmark/leetcode`` that have
    ``tests/testcases.jsonl`` and ``tests/harness.rs``.

    If ``only_missing_mutated`` is True (default), dirs that already have
    ``tests/mutated_testcases.jsonl`` are omitted. Set to False to list every
    eligible problem.
    """
    out = []
    for p in sorted(LEETCODE_DIR.iterdir()):
        if not p.is_dir() or not p.name.startswith("lc"):
            continue
        if (p / "tests" / "testcases.jsonl").exists() and (p / "tests" / "harness.rs").exists():
            if only_missing_mutated and has_mutated_testcases(p):
                continue
            out.append(p)
    return out


def with_temp_workdir(prefix: str = "vcg_mutvar_"):
    """Convenience: returns a TemporaryDirectory context."""
    return tempfile.TemporaryDirectory(prefix=prefix)

"""Helpers for splicing variants into a Codeforces ``main.rs``, compiling, and
running them on stdin/stdout test cases.

Each Codeforces problem has a self-contained ``main.rs`` of the form:

    use std::io::{self, Read};

    struct Solution;
    impl Solution { ... }

    fn main() { ... reads stdin, calls Solution::*, prints stdout ... }

A variant is just a replacement ``impl Solution { ... }`` block (same shape as
``code.rs``). We rebuild the file by replacing the first impl-Solution block.
"""
from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CF_DIR = REPO_ROOT / "benchmark" / "codeforces"

MUTATED_TESTCASES_NAME = "mutated_testcases.jsonl"


def mutated_testcases_path(pdir: Path) -> Path:
    """Path to the per-problem mutated testcase JSONL (may be absent)."""
    return pdir / "tests" / MUTATED_TESTCASES_NAME


def has_mutated_testcases(pdir: Path) -> bool:
    """True if this problem already has a ``mutated_testcases.jsonl`` file."""
    return mutated_testcases_path(pdir).is_file()


@dataclass
class MainParts:
    head: str       # everything up to (and including) ``struct Solution;`` line
    impl_block: str  # the original impl Solution block (kept for reference)
    tail: str       # everything after the impl Solution block


_STRUCT_RE = re.compile(r"^[ \t]*(?:pub\s+)?struct\s+Solution\s*;\s*$", re.MULTILINE)
_IMPL_RE = re.compile(r"^[ \t]*impl\s+Solution\s*\{", re.MULTILINE)


def _find_block_end(src: str, start: int) -> int:
    """Given an index pointing at the opening '{' of an impl block, find the
    matching '}' and return its index + 1."""
    depth = 0
    i = start
    in_str = False
    in_char = False
    while i < len(src):
        c = src[i]
        if not in_str and not in_char:
            if c == '"':
                in_str = True
            elif c == "'":
                in_char = True
            elif c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    return i + 1
        else:
            if in_str and c == "\\" and i + 1 < len(src):
                i += 2
                continue
            if in_str and c == '"':
                in_str = False
            elif in_char and c == "\\" and i + 1 < len(src):
                i += 2
                continue
            elif in_char and c == "'":
                in_char = False
        i += 1
    raise ValueError("unbalanced braces in impl block")


def split_main(main_src: str) -> MainParts:
    m_struct = _STRUCT_RE.search(main_src)
    if not m_struct:
        raise ValueError("main.rs missing 'struct Solution;'")
    m_impl = _IMPL_RE.search(main_src, m_struct.end())
    if not m_impl:
        raise ValueError("main.rs missing 'impl Solution { ... }' after struct decl")
    brace_idx = main_src.index("{", m_impl.start())
    end = _find_block_end(main_src, brace_idx)
    head = main_src[: m_impl.start()]
    impl_block = main_src[m_impl.start(): end]
    tail = main_src[end:]
    return MainParts(head=head, impl_block=impl_block, tail=tail)


def assemble_variant_main(main_src: str, variant_code: str) -> str:
    parts = split_main(main_src)
    return f"{parts.head}{variant_code.strip()}\n{parts.tail}"


def compile_rust(src_path: Path, bin_path: Path, *, timeout: float = 60.0) -> tuple[bool, str]:
    cmd = [
        "rustc",
        "--edition", "2021",
        "-O",
        "-A", "warnings",
        str(src_path),
        "-o", str(bin_path),
    ]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        return False, f"rustc timeout ({timeout}s): {e}"
    return proc.returncode == 0, proc.stderr or proc.stdout


def run_binary(bin_path: Path, stdin_text: str, *, timeout: float = 10.0) -> tuple[bool, str, str]:
    """Run the binary once with ``stdin_text`` on stdin. Returns (ok, stdout, stderr)."""
    try:
        proc = subprocess.run(
            [str(bin_path)],
            input=stdin_text,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False, "", "binary timed out"
    return proc.returncode == 0, proc.stdout, proc.stderr


def normalize_output(s: str) -> str:
    """Whitespace-tolerant normalization for matching CF judge behaviour:
    strip trailing whitespace on each line, collapse trailing blank lines."""
    lines = [ln.rstrip() for ln in s.splitlines()]
    while lines and lines[-1] == "":
        lines.pop()
    return "\n".join(lines)


def list_codeforces_problems(*, only_missing_mutated: bool = True) -> list[Path]:
    """List Codeforces problem dirs under ``benchmark/codeforces`` that have
    ``tests/testcases.jsonl`` and ``main.rs``.

    If ``only_missing_mutated`` is True (default), problems that already have
    ``tests/mutated_testcases.jsonl`` are omitted so mutator pipelines do not
    redo finished work. Set to False to list every eligible problem.
    """
    out = []
    for p in sorted(CF_DIR.iterdir()):
        if not p.is_dir() or not p.name.startswith("cf"):
            continue
        if (p / "tests" / "testcases.jsonl").exists() and (p / "main.rs").exists():
            if only_missing_mutated and has_mutated_testcases(p):
                continue
            out.append(p)
    return out


def load_problem_files(pdir: Path) -> tuple[str, str, str]:
    """(description.md, code.rs, main.rs)"""
    desc = (pdir / "description.md").read_text()
    code = (pdir / "code.rs").read_text()
    main = (pdir / "main.rs").read_text()
    return desc, code, main

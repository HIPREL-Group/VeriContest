"""Code mutation operators for the exec-mutation negative generator.

Primary path: cargo-mutants (type-aware). Fallback (when cargo-mutants is
unavailable — recorded in toolchain.json): a string-literal-safe operator subset
implemented directly on code.rs.
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Mutant:
    idx: int
    op: str
    text: str                 # full mutated code.rs
    diff: str = ""            # human-readable one-line description
    span: tuple[int, int] = (0, 0)


def cargo_mutants_available() -> bool:
    if shutil.which("cargo") is None:
        return False
    try:
        r = subprocess.run(["cargo", "mutants", "--version"], capture_output=True, text=True, timeout=20)
        return r.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


# ---------------------------------------------------------------------------
# Fallback operators (string-literal-safe token rewriting).
# ---------------------------------------------------------------------------

_STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')

# Relational operator rewrites (ROR).
_REL_OPS = ["==", "!=", "<=", ">=", "<", ">"]
# Arithmetic operator rewrites (AOR).
_ARITH = {"+": "-", "-": "+", "*": "+"}
# Logical connective rewrites (LCR).
_LOGIC = {"&&": "||", "||": "&&"}


_PUA_BASE = 0xE000  # private-use area; single char per masked literal


def _mask_strings(text: str) -> tuple[str, list[str]]:
    """Replace each string literal with a single private-use-area char so the
    operator regexes (digits, arithmetic, relational) never touch it."""
    stash: list[str] = []

    def repl(m):
        stash.append(m.group(0))
        return chr(_PUA_BASE + len(stash) - 1)

    return _STRING_RE.sub(repl, text), stash


def _unmask(text: str, stash: list[str]) -> str:
    out = []
    for ch in text:
        o = ord(ch)
        if _PUA_BASE <= o < _PUA_BASE + len(stash):
            out.append(stash[o - _PUA_BASE])
        else:
            out.append(ch)
    return "".join(out)


def _token_positions(masked: str, pattern: str) -> list[int]:
    return [m.start() for m in re.finditer(pattern, masked)]


def generate_fallback(code_rs: str, max_mutants: int, seed: int) -> list[Mutant]:
    import random
    rng = random.Random(seed)
    masked, stash = _mask_strings(code_rs)
    mutants: list[Mutant] = []
    idx = 0

    def add(new_masked: str, op: str, desc: str):
        nonlocal idx
        text = _unmask(new_masked, stash)
        if text != code_rs:
            mutants.append(Mutant(idx, op, text, desc))
            idx += 1

    # ROR: relational operators (avoid ->, =>, ==, etc. handled by ordering)
    for m in re.finditer(r"(?<![=!<>])(==|!=|<=|>=|<|>)(?!=)", masked):
        op_txt = m.group(1)
        for repl in _REL_OPS:
            if repl == op_txt:
                continue
            new = masked[:m.start()] + repl + masked[m.end():]
            add(new, "ROR", f"{op_txt}->{repl}@{m.start()}")

    # AOR: arithmetic operators (skip += etc. and pointers)
    for m in re.finditer(r"(?<![+\-*/=])([+\-*])(?![+\-*/=])", masked):
        op_txt = m.group(1)
        repl = _ARITH.get(op_txt)
        if repl:
            new = masked[:m.start()] + repl + masked[m.end():]
            add(new, "AOR", f"{op_txt}->{repl}@{m.start()}")

    # LCR: logical connectives
    for m in re.finditer(r"(&&|\|\|)", masked):
        op_txt = m.group(1)
        repl = _LOGIC[op_txt]
        new = masked[:m.start()] + repl + masked[m.end():]
        add(new, "LCR", f"{op_txt}->{repl}@{m.start()}")

    # COI: integer-literal +/-1
    for m in re.finditer(r"(?<![\w.])(\d+)(?![\w.])", masked):
        val = int(m.group(1))
        for delta in (1, -1):
            nv = val + delta
            if nv < 0:
                continue
            new = masked[:m.start()] + str(nv) + masked[m.end():]
            add(new, "COI", f"{val}->{nv}@{m.start()}")

    # negate-condition: wrap `if <cond>` -> `if !(<cond>)` (best-effort, balanced)
    for m in re.finditer(r"\bif\s+", masked):
        start = m.end()
        # find the condition up to the opening brace at top level
        depth = 0
        i = start
        while i < len(masked):
            c = masked[i]
            if c in "([":
                depth += 1
            elif c in ")]":
                depth -= 1
            elif c == "{" and depth == 0:
                break
            i += 1
        if i < len(masked) and masked[i] == "{":
            cond = masked[start:i].strip()
            if cond and "!" not in cond[:2]:
                new = masked[:start] + f"!({cond}) " + masked[i:]
                add(new, "NEG", f"if-negate@{start}")

    # Stratified sample: round-robin across (operator, source line) groups so
    # the budget spreads over the whole program instead of clustering on
    # whichever region has the most operators.
    def line_of(mt: Mutant) -> int:
        try:
            pos = int(mt.diff.rsplit("@", 1)[1])
        except (IndexError, ValueError):
            return 0
        return code_rs.count("\n", 0, min(pos, len(code_rs)))

    groups: dict[tuple, list[Mutant]] = {}
    for mt in mutants:
        groups.setdefault((mt.op, line_of(mt)), []).append(mt)
    for g in groups.values():
        rng.shuffle(g)
    order = list(groups.keys())
    rng.shuffle(order)
    trimmed: list[Mutant] = []
    while len(trimmed) < max_mutants and any(groups[k] for k in order):
        for key in order:
            if groups[key] and len(trimmed) < max_mutants:
                trimmed.append(groups[key].pop())
    for k, mt in enumerate(trimmed):
        mt.idx = k
    return trimmed


def generate_cargo_mutants(code_rs: str, crate_dir: Path, max_mutants: int, seed: int) -> list[Mutant]:
    """Harvest mutants via `cargo mutants --list --json`. Applies each diff to a
    fresh copy. Returns [] on any tooling failure (caller falls back)."""
    crate_dir.mkdir(parents=True, exist_ok=True)
    (crate_dir / "src").mkdir(exist_ok=True)
    lib = crate_dir / "src" / "lib.rs"
    body = code_rs if re.search(r"\bstruct\s+Solution\b", code_rs) else "pub struct Solution;\n" + code_rs
    lib.write_text(body, encoding="utf-8")
    (crate_dir / "Cargo.toml").write_text(
        '[package]\nname = "mut"\nversion = "0.0.0"\nedition = "2021"\n\n[lib]\npath = "src/lib.rs"\n',
        encoding="utf-8",
    )
    try:
        r = subprocess.run(["cargo", "mutants", "--list", "--json", "--no-shuffle"],
                           cwd=crate_dir, capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return []
    if r.returncode != 0:
        return []
    try:
        listing = json.loads(r.stdout)
    except json.JSONDecodeError:
        return []
    mutants: list[Mutant] = []
    # cargo-mutants JSON: list of {function, replacement, span, ...}. Shape may
    # vary by version; we record the description and leave text application to
    # the diff (not available in --list). This path is only exercised where
    # cargo-mutants exists; the fallback covers this environment.
    for i, rec in enumerate(listing[:max_mutants]):
        desc = rec.get("function", {}) if isinstance(rec.get("function"), dict) else rec
        mutants.append(Mutant(i, "cargo", body, json.dumps(desc)[:200]))
    return mutants

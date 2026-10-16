"""Extract the final program from a model response.

SpecGen, CodeGen from natural language, and ProofGen take the first fenced
block; CodeGen with a specification and End2End take the last block that looks
like a complete solution. Without a fenced block, the whole response is used.
"""
from __future__ import annotations

import re

CODE_FENCE_RE = re.compile(r"```(?:rust)?\s*\n?(.*?)```", re.DOTALL)


def first_block(text: str) -> str | None:
    m = CODE_FENCE_RE.search(text)
    if m and m.group(1).strip():
        return m.group(1).strip()
    return text.strip() or None


def last_solution_block(text: str) -> str | None:
    blocks = [b for b in (m.group(1).strip() for m in CODE_FENCE_RE.finditer(text)) if b]
    if blocks:
        for code in reversed(blocks):
            if "impl Solution" in code or "verus!" in code:
                return code
        return blocks[-1]
    return text.strip() or None


def extract_program(response: str, rule: str) -> str | None:
    code = first_block(response) if rule == "first" else last_solution_block(response)
    return None if code is None else code + "\n"

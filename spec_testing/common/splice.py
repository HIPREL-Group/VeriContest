"""Robust ensures-block splicing on verified.rs text (used by the sanity
`ensures false` vacuity probe).

The clause region runs from the top-level `ensures` keyword to the first
top-level `decreases`/`recommends` keyword or the fn body brace — "top-level"
meaning at zero (paren/bracket/brace) depth, so clauses containing blocks like
`p ==> ({ ... })` are never cut through.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass

from .config import REPO_ROOT

_POST2EXE = str(REPO_ROOT / "post2exe")
if _POST2EXE not in sys.path:
    sys.path.insert(0, _POST2EXE)

import gen_test_post as gtp  # noqa: E402


@dataclass
class EnsuresSpan:
    clause_start: int      # index just after the `ensures` keyword
    clause_end: int        # index of the char after the last clause (exclusive)


_STOP_KEYWORDS = ("decreases", "recommends")


def _mask_strings(text: str) -> str:
    """Replace string/char literal contents with spaces (positions preserved)."""
    out = list(text)
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == '"':
            j = i + 1
            while j < len(text):
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    break
                j += 1
            for k in range(i + 1, min(j, len(text))):
                out[k] = " "
            i = j + 1
        elif ch == "'" and i + 2 < len(text) and (text[i + 1] == "\\" or text[i + 2] == "'"):
            j = text.find("'", i + 1 + (2 if text[i + 1] == "\\" else 1))
            if j == -1:
                i += 1
                continue
            for k in range(i + 1, j):
                out[k] = " "
            i = j + 1
        else:
            i += 1
    return "".join(out)


def find_ensures_span(text: str, fn_name: str) -> EnsuresSpan | None:
    for m in re.finditer(gtp.FN_HEAD_RE, text):
        if m.group("name") != fn_name:
            continue
        prefix = text[max(0, m.start() - 64): m.start()]
        if not gtp.is_exec_fn_prefix(prefix):
            continue
        close_paren = gtp.find_matching_paren(text, m.end() - 1)
        if close_paren == -1:
            return None
        # bound the search region to before the next fn head
        nxt = None
        for mm in re.finditer(gtp.FN_HEAD_RE, text):
            if mm.start() > close_paren:
                nxt = mm.start()
                break
        region_end = nxt if nxt is not None else len(text)
        body_open, _ = gtp.find_fn_body_brace(text[:region_end], close_paren + 1)
        if body_open == -1:
            return None

        header = text[close_paren + 1:body_open]
        masked = _mask_strings(header)

        # locate the top-level `ensures` keyword
        depth = 0
        ens_off = None
        i = 0
        while i < len(masked):
            ch = masked[i]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0 and masked.startswith("ensures", i) and \
                    (i == 0 or not (masked[i - 1].isalnum() or masked[i - 1] == "_")) and \
                    (i + 7 >= len(masked) or not (masked[i + 7].isalnum() or masked[i + 7] == "_")):
                ens_off = i
                break
            i += 1
        if ens_off is None:
            return None
        clause_start = close_paren + 1 + ens_off + len("ensures")

        # clause region ends at the first top-level stop keyword after ensures
        depth = 0
        end_off = len(masked)
        i = ens_off + len("ensures")
        while i < len(masked):
            ch = masked[i]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0:
                for kw in _STOP_KEYWORDS:
                    if masked.startswith(kw, i) and \
                            not (masked[i - 1].isalnum() or masked[i - 1] == "_") and \
                            (i + len(kw) >= len(masked) or
                             not (masked[i + len(kw)].isalnum() or masked[i + len(kw)] == "_")):
                        end_off = i
                        break
                if end_off != len(masked):
                    break
            i += 1
        clause_end = close_paren + 1 + end_off
        return EnsuresSpan(clause_start, clause_end)
    return None


def replace_ensures(text: str, fn_name: str, new_clauses: list[str]) -> str | None:
    """Replace the fn's whole ensures clause list with `new_clauses`."""
    span = find_ensures_span(text, fn_name)
    if span is None:
        return None
    rendered = "\n            " + ",\n            ".join(new_clauses) + ",\n        "
    return text[:span.clause_start] + rendered + text[span.clause_end:]

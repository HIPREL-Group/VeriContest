#!/usr/bin/env python3
"""
Generate `test_post.rs` for each problem by extracting the postcondition from
`spec.rs`/`code_spec.rs` and lowering it into the restricted
`exec_spec_unverified!` surface syntax.

Conceptually this script does three things:
1. Parse the target function signature plus its `ensures`/`returns` clause.
2. Pull in every helper `spec fn` the postcondition depends on.
3. Normalize the collected spec text until the proc macro can compile it.

The generated file can then be compiled with `verus --compile` to answer one
question: "is this postcondition executable enough to run as Rust?"

Usage
-----
    python post2exe/gen_test_post.py --all
    python post2exe/gen_test_post.py --kind leetcode
    python post2exe/gen_test_post.py --problem benchmark/leetcode/lc986
    python post2exe/gen_test_post.py --all --force
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH_ROOT = REPO_ROOT / "benchmark"

# ---------------------------------------------------------------------------
# Signature parsing (reused from scaffold_mutants.py)
# ---------------------------------------------------------------------------

@dataclass
class Signature:
    method: str
    args: list[tuple[str, str]]   # [(name, type), ...]
    ret: str                      # "()" if none
    receiver: str | None = None


RET_NAMED_RE = re.compile(r"\(\s*(\w+)\s*:\s*(.+)\s*\)")


def split_signature_args(args_raw: str) -> list[str]:
    if not args_raw.strip():
        return []
    depth_angle = depth_paren = depth_brack = depth_brace = 0
    parts: list[str] = []
    cur = ""
    for ch in args_raw:
        if ch == "<":
            depth_angle += 1
        elif ch == ">":
            depth_angle -= 1
        elif ch == "(":
            depth_paren += 1
        elif ch == ")":
            depth_paren -= 1
        elif ch == "[":
            depth_brack += 1
        elif ch == "]":
            depth_brack -= 1
        elif ch == "{":
            depth_brace += 1
        elif ch == "}":
            depth_brace -= 1
        if (
            ch == ","
            and depth_angle == 0
            and depth_paren == 0
            and depth_brack == 0
            and depth_brace == 0
        ):
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return [p.strip() for p in parts if p.strip()]


def parse_signature_from_region(
    text: str,
    fn_name: str,
    open_paren: int,
) -> Signature:
    close_paren = find_matching_paren(text, open_paren)
    if close_paren == -1:
        raise ValueError(f"unterminated parameter list for `{fn_name}`")
    args_raw = text[open_paren + 1 : close_paren].strip()
    args: list[tuple[str, str]] = []
    receiver: str | None = None
    for p in split_signature_args(args_raw):
        if ":" not in p:
            if re.fullmatch(r"(?:&mut\s+|&\s*|mut\s+)?self", p):
                receiver = p
                continue
            raise ValueError(f"cannot parse arg fragment: {p!r}")
        n, t = p.split(":", 1)
        args.append((n.strip(), t.strip()))

    rest = text[close_paren + 1 :]
    ret = "()"
    if rest.lstrip().startswith("->"):
        arrow = close_paren + 1 + rest.index("->")
        ret_start = arrow + 2
        ret_text = text[ret_start:]
        cutoffs = []
        for kw in ("requires", "ensures", "returns", "decreases", "{"):
            m = re.search(rf"\b{kw}\b", ret_text)
            if m:
                cutoffs.append(m.start())
        if cutoffs:
            ret_text = ret_text[: min(cutoffs)]
        ret = ret_text.strip() or "()"

    return Signature(method=fn_name, args=args, ret=ret, receiver=receiver)


FN_HEAD_RE = re.compile(r"\bfn\s+(?P<name>\w+)\s*\(")


def is_exec_fn_prefix(prefix: str) -> bool:
    return not re.search(r"(?:^|[\s{])(spec|proof)\s*$", prefix)


def parse_signature(text: str, fn_name: str | None = None) -> Signature:
    for m in FN_HEAD_RE.finditer(text):
        name = m.group("name")
        if fn_name is not None and name != fn_name:
            continue
        prefix = text[max(0, m.start() - 64) : m.start()]
        if not is_exec_fn_prefix(prefix):
            continue
        return parse_signature_from_region(text, name, m.end() - 1)
    if fn_name is None:
        raise ValueError("no executable `fn` signature found")
    raise ValueError(f"no signature found for `{fn_name}`")


def parse_return(ret_raw: str) -> tuple[str, str]:
    """Parse ``(name: Type)`` -> (name, Type), or plain Type -> ("result", Type)."""
    ret_raw = ret_raw.strip()
    m = RET_NAMED_RE.match(ret_raw)
    if m:
        return m.group(1).strip(), m.group(2).strip()
    return "result", ret_raw


# ---------------------------------------------------------------------------
# Verus spec-code extraction
# ---------------------------------------------------------------------------

# Some benchmarks hide helper definitions behind `closed spec fn`, or omit the
# openness marker entirely.  The generator only needs the executable body text,
# so we collect any public spec helper regardless of whether Verus marks it
# `open`, `closed`, or leaves the default visibility in place.
SPEC_FN_HEAD_RE = re.compile(r"pub\s+(?:(?:open|closed)\s+)?spec\s+fn\s+(\w+)")


def find_matching_brace(text: str, start: int) -> int:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return i
    return -1


def extract_verus_block(spec_text: str) -> str:
    """Return the inner text of ``verus! { ... }``."""
    m = re.search(r"verus!\s*\{", spec_text)
    if not m:
        return ""
    brace_start = spec_text.index("{", m.start())
    brace_end = find_matching_brace(spec_text, brace_start)
    if brace_end == -1:
        return ""
    return spec_text[brace_start + 1 : brace_end]


def extract_impl_block(verus_text: str) -> str:
    """Return the inner text of ``impl Solution { ... }``."""
    m = re.search(r"impl\s+Solution\s*\{", verus_text)
    if not m:
        return ""
    brace_start = verus_text.index("{", m.start())
    brace_end = find_matching_brace(verus_text, brace_start)
    if brace_end == -1:
        return ""
    return verus_text[brace_start + 1 : brace_end]


def iter_postcondition_fns(
    text: str,
) -> list[tuple[str, list[str], str | None]]:
    """Return exec fns with ensures/returns in *text* in source order."""
    found: list[tuple[str, list[str], str | None]] = []
    for m in FN_HEAD_RE.finditer(text):
        prefix = text[max(0, m.start() - 64) : m.start()]
        if not is_exec_fn_prefix(prefix):
            continue

        close_paren = find_matching_paren(text, m.end() - 1)
        if close_paren == -1:
            continue

        rest = text[close_paren + 1 :]
        ens_match = re.search(r"\bensures\b", rest)
        ret_match = None if ens_match else re.search(r"\breturns\b", rest)
        if ens_match is None and ret_match is None:
            continue

        match = ens_match or ret_match
        body_open, _ = find_fn_body_brace(text, close_paren + 1)
        if body_open == -1:
            continue
        post_start = close_paren + 1 + match.end()
        post_text = text[post_start:body_open].strip().rstrip(",").strip()
        if ens_match is not None:
            clauses = split_top_level(post_text)
            found.append(
                (
                    m.group("name"),
                    [
                        c.strip().rstrip(",").strip()
                        for c in clauses
                        if c.strip().rstrip(",").strip()
                    ],
                    None,
                )
            )
        else:
            found.append((m.group("name"), [], post_text))
    return found


def extract_requires_clauses(text: str, fn_name: str) -> list[str]:
    """Return the requires clauses for *fn_name* in source order, if any."""
    for m in FN_HEAD_RE.finditer(text):
        if m.group("name") != fn_name:
            continue
        prefix = text[max(0, m.start() - 64) : m.start()]
        if not is_exec_fn_prefix(prefix):
            continue
        close_paren = find_matching_paren(text, m.end() - 1)
        if close_paren == -1:
            continue
        body_open, _ = find_fn_body_brace(text, close_paren + 1)
        if body_open == -1:
            continue
        clause_region = text[close_paren + 1 : body_open]
        # Find `requires` keyword and the text up to the next top-level
        # keyword (`ensures`, `returns`, `decreases`) or end-of-region.
        req_match = re.search(r"\brequires\b", clause_region)
        if req_match is None:
            return []
        start = req_match.end()
        rest = clause_region[start:]
        # Find earliest position of any other keyword.
        end = len(rest)
        for kw in ("ensures", "returns", "decreases"):
            km = re.search(rf"\b{kw}\b", rest)
            if km is not None and km.start() < end:
                end = km.start()
        req_text = rest[:end].strip().rstrip(",").strip()
        if not req_text:
            return []
        clauses = split_top_level(req_text)
        return [
            c.strip().rstrip(",").strip()
            for c in clauses
            if c.strip().rstrip(",").strip()
        ]
    return []


def choose_target_fn(verus_text: str) -> tuple[str | None, list[str], str | None]:
    """Choose the primary ensured function to scaffold for this spec."""
    impl_text = extract_impl_block(verus_text)
    if impl_text:
        impl_candidates = iter_postcondition_fns(impl_text)
        if impl_candidates:
            return impl_candidates[-1]

    all_candidates = iter_postcondition_fns(verus_text)
    if all_candidates:
        return all_candidates[-1]
    return None, [], None


def extract_use_lines(text: str) -> list[str]:
    seen: set[str] = set()
    lines: list[str] = []
    for m in re.finditer(r"^\s*use\s+[^;]+;\s*$", text, re.MULTILINE):
        line = m.group(0).strip()
        if line not in seen:
            seen.add(line)
            lines.append(line)
    return lines


def extract_const_lines(text: str) -> list[str]:
    seen: set[str] = set()
    lines: list[str] = []
    for m in re.finditer(
        r"^\s*(?:pub\s+)?const\s+\w+\s*:\s*[^=;]+\s*=\s*[^;]+;\s*$",
        text,
        re.MULTILINE,
    ):
        line = m.group(0).strip()
        line = re.sub(r"^pub\s+", "", line)
        if line not in seen:
            seen.add(line)
            lines.append(line)
    return lines


def find_fn_body_brace(text: str, start: int) -> tuple[int, int]:
    """Find the actual function body ``{ ... }`` range.

    Verus clauses may contain top-level brace pairs before the real body, for
    example ``ensures p ==> { exists|...| ... }`` or ``decreases if cond { ... }
    else { ... }``.  The actual body is the last top-level brace pair attached
    to the function item, so we scan all such pairs and return the final one.
    """
    pos = start
    last_open = -1
    last_close = -1
    while pos < len(text):
        ch = text[pos]
        if ch == "{":
            end = find_matching_brace(text, pos)
            if end == -1:
                break
            last_open = pos
            last_close = end
            pos = end + 1
        elif ch == "}":
            break
        else:
            pos += 1
    return last_open, last_close


def extract_spec_fns(text: str) -> dict[str, str]:
    """Return {name: full_text} for every public spec helper in *text*.

    *text* can be the full verus block; spec fns are found both inside
    and outside ``impl Solution``.
    """
    fns: dict[str, str] = {}
    for m in SPEC_FN_HEAD_RE.finditer(text):
        name = m.group(1)
        body_open, body_close = find_fn_body_brace(text, m.end())
        if body_open == -1 or body_close == -1:
            continue
        fns[name] = text[m.start() : body_close + 1]
    return fns


def split_top_level(text: str, sep: str = ",") -> list[str]:
    """Split *text* by *sep* not inside ``()[]{}||``.

    ``<>`` are NOT tracked as brackets because ``<``/``>`` also appear as
    comparison operators in ensures/requires clauses.  Generic angle
    brackets in type positions (e.g. ``Vec<i32>``) do not contain commas,
    so ignoring them for depth-tracking is safe for clause splitting.
    """
    depth = 0
    pipe_depth = 0
    parts: list[str] = []
    current = ""
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "|":
            pipe_depth = 1 - pipe_depth
        if ch == sep and depth == 0 and pipe_depth == 0:
            parts.append(current)
            current = ""
        else:
            current += ch
    if current.strip():
        parts.append(current)
    return parts


def split_top_level_op(text: str, op: str) -> list[str]:
    """Split *text* by a multi-char operator at top level."""
    depth = 0
    pipe_depth = 0
    parts: list[str] = []
    current = ""
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "|":
            pipe_depth = 1 - pipe_depth

        if depth == 0 and pipe_depth == 0 and text.startswith(op, i):
            parts.append(current)
            current = ""
            i += len(op)
            continue

        current += ch
        i += 1

    if current.strip():
        parts.append(current)
    return parts


def split_once_top_level(text: str, op: str) -> tuple[str, str] | None:
    """Split *text* once on the first top-level occurrence of *op*."""
    depth = 0
    pipe_depth = 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "|":
            pipe_depth = 1 - pipe_depth

        if depth == 0 and pipe_depth == 0 and text.startswith(op, i):
            return text[:i], text[i + len(op) :]
        i += 1
    return None


def extract_ensures_clauses(text: str) -> tuple[str | None, list[str]]:
    """Return (fn_name, [clause, ...]) for the primary exec fn in *text*."""
    fn_name, clauses, _ = choose_target_fn(text)
    return fn_name, clauses


def normalize_quantifier_body(kind: str, binders: str, body: str) -> str:
    """Reshape quantifier bodies to match exec_spec_unverified!'s strict parser."""
    binder_parts = [p.strip() for p in split_top_level(binders) if p.strip()]
    var_count = len(binder_parts)
    binder_names = [p.split(":", 1)[0].strip() for p in binder_parts if ":" in p]
    body = body.strip()
    if var_count == 0 or not body:
        return body

    def maybe_expand_two_var_chain(expr: str) -> list[str] | None:
        if len(binder_names) != 2:
            return None
        v1, v2 = binder_names
        m = re.match(
            rf"^\s*(?P<lower>.+?)\s*(?P<op1><=|<)\s*{re.escape(v1)}\s*"
            rf"(?P<op2><=|<)\s*{re.escape(v2)}\s*(?P<op3><=|<)\s*"
            rf"(?P<upper>.+?)\s*$",
            expr,
            re.DOTALL,
        )
        if not m:
            return None
        g1 = f"{m.group('lower').strip()} {m.group('op1')} {v1} {m.group('op3')} {m.group('upper').strip()}"
        g2 = f"{v1} {m.group('op2')} {v2} {m.group('op3')} {m.group('upper').strip()}"
        return [g1, g2]

    def expand_guard_like_parts(parts: list[str]) -> list[str]:
        expanded: list[str] = []
        for part in parts:
            chain = maybe_expand_two_var_chain(part)
            if chain is not None:
                expanded.extend(chain)
            else:
                expanded.append(part.strip())
        return expanded

    def merge_single_var_range(parts: list[str]) -> tuple[str | None, list[str]]:
        if len(binder_names) != 1:
            return None, parts
        var = binder_names[0]
        lower_idx = upper_idx = None
        lower = upper = None
        for idx, part in enumerate(parts):
            m = re.fullmatch(
                rf"(.+?)\s*(<=|<)\s*{re.escape(var)}",
                strip_balanced_parens(part),
                re.DOTALL,
            )
            if m and lower is None:
                lower_idx = idx
                lower = (m.group(1).strip(), m.group(2))
                continue
            m = re.fullmatch(
                rf"{re.escape(var)}\s*(<=|<)\s*(.+)",
                strip_balanced_parens(part),
                re.DOTALL,
            )
            if m and upper is None:
                upper_idx = idx
                upper = (m.group(1), m.group(2).strip())
        if lower is None or upper is None:
            return None, parts
        remaining = [
            p for idx, p in enumerate(parts) if idx not in {lower_idx, upper_idx}
        ]
        merged = f"{lower[0]} {lower[1]} {var} {upper[0]} {upper[1]}"
        return merged, remaining

    if kind == "exists":
        # `exists` is the stricter case for the macro: it expects the leading
        # conjuncts to be simple range guards, and everything after that to be
        # the witness body.  This pass rewrites looser Verus shapes into that
        # prefix form without trying to prove equivalence beyond syntax.
        parts = expand_guard_like_parts(
            [p.strip() for p in split_top_level_op(body, "&&")]
        )
        if len(parts) < var_count:
            expanded = maybe_expand_two_var_chain(body)
            if expanded is not None:
                parts = expanded
        merged_guard, remaining_parts = merge_single_var_range(parts)
        if merged_guard is not None:
            if remaining_parts:
                return f"{merged_guard} && ({' && '.join(remaining_parts)})"
            return merged_guard
        if len(parts) > var_count:
            guards = " && ".join(parts[:var_count])
            rest = " && ".join(parts[var_count:])
            return f"{guards} && ({rest})"
        return body

    if kind == "forall":
        # For `forall`, the macro expects "guards ==> body".  If the original
        # antecedent mixes range guards with extra predicates, we keep the first
        # N guard-like pieces in the prefix and re-nest the remaining pieces
        # under another implication.
        split = split_once_top_level(body, "==>")
        if split is None:
            return body
        antecedent, consequent = split
        ant_parts = expand_guard_like_parts(
            [p.strip() for p in split_top_level_op(antecedent, "&&")]
        )
        if len(ant_parts) < var_count:
            expanded = maybe_expand_two_var_chain(antecedent)
            if expanded is not None:
                ant_parts = expanded
        merged_guard, remaining_parts = merge_single_var_range(ant_parts)
        if merged_guard is not None:
            if remaining_parts:
                rest = " && ".join(remaining_parts)
                return f"{merged_guard} ==> ({rest} ==> {consequent.strip()})"
            return f"{merged_guard} ==> {consequent.strip()}"
        if len(ant_parts) > var_count:
            guards = " && ".join(ant_parts[:var_count])
            rest = " && ".join(ant_parts[var_count:])
            return f"{guards} ==> ({rest} ==> {consequent.strip()})"
        if len(ant_parts) == var_count and ant_parts != [antecedent.strip()]:
            guards = " && ".join(ant_parts)
            return f"{guards} ==> {consequent.strip()}"
        return body

    return body


def maybe_expand_bool_quantifier(
    kind: str,
    binders: str,
    body: str,
) -> str | None:
    """Eliminate bool binders by finite expansion.

    The macro only executes quantifiers over concrete finite domains with range
    guards.  `bool` has only two values, so instead of trying to teach the macro
    about booleans we simply enumerate the cases here.
    """
    binder_parts = [p.strip() for p in split_top_level(binders) if p.strip()]
    if not binder_parts:
        return None

    bool_binders: list[str] = []
    other_binders: list[str] = []
    for part in binder_parts:
        if ":" not in part:
            return None
        name, ty = [x.strip() for x in part.split(":", 1)]
        if ty == "bool":
            bool_binders.append(name)
        else:
            other_binders.append(part)

    if not bool_binders:
        return None

    assignments = [()]
    for _ in bool_binders:
        assignments = [vals + (False,) for vals in assignments] + [
            vals + (True,) for vals in assignments
        ]

    terms: list[str] = []
    for values in assignments:
        expanded_body = body
        for name, value in zip(bool_binders, values):
            lit = "true" if value else "false"
            expanded_body = re.sub(
                rf"\b{re.escape(name)}\b",
                lit,
                expanded_body,
            )
        expanded_body = expanded_body.strip()
        if other_binders:
            other_binders_text = ", ".join(other_binders)
            expanded_body = normalize_quantifier_body(
                kind,
                other_binders_text,
                expanded_body,
            )
            terms.append(f"({kind} |{other_binders_text}| {expanded_body})")
        else:
            terms.append(f"({expanded_body})")

    joiner = " && " if kind == "forall" else " || "
    return joiner.join(terms)


def find_first_call_span(expr: str, binder_names: list[str]) -> tuple[int, int] | None:
    """Return the earliest call that mentions a quantified variable.

    Trigger injection is purely heuristic in this script.  We look for the first
    term that is likely to be a useful trigger, preferring a concrete index
    expression elsewhere when one exists.
    """
    i = 0
    while i < len(expr):
        if expr[i].isalpha() or expr[i] == "_":
            j = i + 1
            while j < len(expr) and (expr[j].isalnum() or expr[j] == "_"):
                j += 1
            k = j
            while k < len(expr) and expr[k].isspace():
                k += 1
            if k < len(expr) and expr[k] == "(":
                end = find_matching_paren(expr, k)
                if end != -1:
                    term = expr[i : end + 1]
                    if any(
                        re.search(rf"\b{re.escape(name)}\b", term)
                        for name in binder_names
                    ):
                        return i, end + 1
                    i = end + 1
                    continue
        i += 1
    return None


def add_trigger_to_expr(expr: str, binder_names: list[str]) -> str:
    """Inject a single `#[trigger]` on the first usable quantified term."""
    if "#[trigger]" in expr:
        return expr

    index_match = None
    for m in re.finditer(r"\b[A-Za-z_]\w*(?:\[[^\[\]]+\])+", expr):
        term = m.group(0)
        if any(re.search(rf"\b{re.escape(name)}\b", term) for name in binder_names):
            index_match = (m.start(), m.end())
            break

    call_match = find_first_call_span(expr, binder_names)
    match = index_match
    if call_match is not None and (
        match is None or call_match[0] < match[0]
    ):
        match = call_match

    if match is None:
        return expr
    return expr[: match[0]] + "#[trigger] " + expr[match[0] :]


def inject_trigger_into_quantifier(kind: str, binders: str, body: str) -> str:
    binder_names = [
        p.split(":", 1)[0].strip()
        for p in split_top_level(binders)
        if ":" in p
    ]
    if not binder_names or "#[trigger]" in body:
        return body

    if kind == "forall":
        split = split_once_top_level(body, "==>")
        if split is None:
            return body
        antecedent, consequent = split
        return f"{antecedent.strip()} ==> {add_trigger_to_expr(consequent.strip(), binder_names)}"

    parts = [p.strip() for p in split_top_level_op(body, "&&") if p.strip()]
    if len(parts) <= len(binder_names):
        return body
    rest = parts[len(binder_names) :]
    rest[0] = add_trigger_to_expr(rest[0], binder_names)
    return " && ".join(parts[: len(binder_names)] + rest)


def normalize_big_boolean_blocks(text: str) -> str:
    """Rewrite line-oriented `&&&` / `|||` blocks into plain `&&` / `||`.

    Verus often writes big conjunctions/disjunctions as:

        &&& cond1
        &&& cond2

    The macro accepts ordinary boolean operators, so we flatten only the
    line-leading big-boolean syntax here and leave inner expressions alone.
    """
    lines = text.splitlines()
    out: list[str] = []
    chain_active = False
    chain_indent = ""
    chain_op = ""
    prev_sig = ""

    for line in lines:
        stripped = line.lstrip()
        indent = line[: len(line) - len(stripped)]
        if stripped.startswith("&&&") or stripped.startswith("|||"):
            op = "&&" if stripped.startswith("&&&") else "||"
            rest = stripped[3:].lstrip()
            can_strip = (
                not prev_sig
                or prev_sig.endswith("{")
                or prev_sig.endswith(";")
                or prev_sig.endswith("(")
            )
            if chain_active and indent == chain_indent and op == chain_op:
                out.append(f"{indent}{op} {rest}" if rest else f"{indent}{op}")
            elif can_strip:
                out.append(f"{indent}{rest}")
                chain_active = True
                chain_indent = indent
                chain_op = op
            else:
                out.append(f"{indent}{op} {rest}" if rest else f"{indent}{op}")
                chain_active = True
                chain_indent = indent
                chain_op = op
            prev_sig = rest or op
            continue

        out.append(line)
        if not stripped:
            continue
        prev_sig = stripped
        if (
            stripped == "}"
            or stripped.endswith("{")
            or stripped.endswith(";")
            or stripped.endswith(",")
        ):
            chain_active = False
            chain_indent = ""
            chain_op = ""

    return "\n".join(out)


def normalize_quantifier_in_text_fragment(text: str) -> str:
    """Normalize the first quantifier found in *text* if present."""
    m = re.search(r"\b(forall|exists)\s*\|([^|]+)\|", text)
    if not m:
        return text
    kind = m.group(1)
    binders = m.group(2)
    prefix = text[: m.start()]
    body = text[m.end() :].strip()
    expanded = maybe_expand_bool_quantifier(kind, binders, body)
    if expanded is not None:
        return f"{prefix}{expanded}"
    normalized = normalize_quantifier_body(kind, binders, body)
    normalized = inject_trigger_into_quantifier(kind, binders, normalized)
    return f"{prefix}{kind} |{binders}| {normalized}"


def normalize_quantifiers_in_clause(clause: str) -> str:
    """Normalize quantifier syntax inside a whole ensures clause."""
    return normalize_quantifiers_in_text(clause)


def normalize_quantifiers_in_text(text: str) -> str:
    """Normalize simple inline quantifiers in helper spec fns."""
    text = normalize_big_boolean_blocks(text)
    lines: list[str] = []
    for line in text.splitlines():
        if "forall" in line or "exists" in line:
            lines.append(normalize_quantifier_in_text_fragment(line))
        elif should_normalize_boolean_line(line):
            lines.append(normalize_simple_chain(line))
        else:
            lines.append(line)
    return "\n".join(lines)


def strip_balanced_parens(expr: str) -> str:
    expr = expr.strip()
    while expr.startswith("(") and expr.endswith(")"):
        depth = 0
        wraps_all = True
        for i, ch in enumerate(expr):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(expr) - 1:
                    wraps_all = False
                    break
        if depth != 0 or not wraps_all:
            break
        expr = expr[1:-1].strip()
    return expr


def strip_trigger_prefix(expr: str) -> str:
    return re.sub(r"^\s*#\[\s*trigger\s*\]\s*", "", expr).strip()


def rewrite_nonnegative_len_comparisons(expr: str) -> str:
    if expr.strip().endswith(("&&", "||")):
        return expr
    parts = split_top_level_op(expr, "&&")
    if len(parts) > 1:
        nonnegative_keys: set[str] = set()
        changed = False
        for part in parts:
            candidate = strip_balanced_parens(part)
            m = re.fullmatch(r"0\s*<=\s*(.+)", candidate)
            if m:
                key = strip_trigger_prefix(strip_balanced_parens(m.group(1)))
                nonnegative_keys.add(key)

        rewritten: list[str] = []
        for part in parts:
            candidate = strip_balanced_parens(part)
            m = re.fullmatch(r"(.+?)\s*(<=|<)\s*(.+?\.len\(\))", candidate)
            if m:
                lhs = m.group(1).strip()
                lhs_key = strip_trigger_prefix(strip_balanced_parens(lhs))
                if lhs_key in nonnegative_keys:
                    cmp = f"(({lhs}) as usize) {m.group(2)} {m.group(3).strip()}"
                    if part.strip().startswith("(") and part.strip().endswith(")"):
                        part = f"({cmp})"
                    else:
                        part = cmp
                    changed = True
            rewritten.append(part.strip())
        if changed:
            return " && ".join(rewritten)
    return expr


def split_comparison_chain(expr: str) -> tuple[list[str], list[str]] | None:
    if "::" in expr or "=~=" in expr:
        return None
    depth = 0
    pipe_depth = 0
    parts: list[str] = []
    ops: list[str] = []
    start = 0
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "|":
            pipe_depth = 1 - pipe_depth

        if depth == 0 and pipe_depth == 0:
            op = None
            if expr.startswith("<=", i):
                op = "<="
            elif expr.startswith(">=", i):
                op = ">="
            elif ch in "<>":
                op = ch
            if op is not None:
                part = expr[start:i].strip()
                if not part:
                    return None
                parts.append(part)
                ops.append(op)
                i += len(op)
                start = i
                continue
        i += 1

    tail = expr[start:].strip()
    if not tail or len(ops) < 2:
        return None
    parts.append(tail)
    return parts, ops


def wrap_boolean_part(expr: str) -> str:
    expr = expr.strip()
    if not expr:
        return expr
    if expr.startswith("(") and expr.endswith(")"):
        return expr
    if " && " in expr or " || " in expr:
        return f"({expr})"
    return expr


def normalize_simple_chain_core(expr: str) -> str:
    if any(tok in expr for tok in ("==>", "<==", "<==>", "|||", "&&&")):
        return expr
    if any(tok in expr for tok in ("{", "}", "if ", " let ")):
        return expr
    parts = split_top_level_op(expr, "||")
    if len(parts) > 1:
        normalized = " || ".join(
            wrap_boolean_part(normalize_simple_chain_core(p.strip()))
            for p in parts
        )
        return normalized
    parts = split_top_level_op(expr, "&&")
    if len(parts) > 1:
        normalized = " && ".join(
            wrap_boolean_part(normalize_simple_chain_core(p.strip()))
            for p in parts
        )
        return rewrite_nonnegative_len_comparisons(normalized)
    if "->" in expr or re.search(r"\b\w+\s*:\s*[^:]", expr):
        return expr
    chain = split_comparison_chain(expr)
    if chain is None:
        return expr
    parts, ops = chain
    rewritten = " && ".join(
        f"({parts[i]} {ops[i]} {parts[i + 1]})"
        for i in range(len(ops))
    )
    return rewrite_nonnegative_len_comparisons(rewritten)


def normalize_simple_chain(expr: str) -> str:
    """Expand non-quantifier chained comparisons into explicit boolean conjunctions."""
    if not expr.strip():
        return expr
    indent = re.match(r"\s*", expr).group(0)
    stripped = expr.strip()
    suffix = ""
    if stripped.endswith(","):
        suffix = ","
        stripped = stripped[:-1].rstrip()
    return f"{indent}{normalize_simple_chain_core(stripped)}{suffix}"


def should_normalize_boolean_line(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return False
    if "::<" in stripped:
        return False
    if stripped.endswith(("&&", "||", "==>")):
        return False
    if stripped in {"{", "}"} or stripped.endswith("{"):
        return False
    if stripped.startswith(
        (
            "&&&",
            "|||",
            "spec fn ",
            "pub open spec fn ",
            "recommends",
            "requires",
            "ensures",
            "decreases",
            "if ",
            "else",
            "let ",
            "pub fn ",
            "fn ",
            "use ",
        )
    ):
        return False
    return any(op in stripped for op in ("<", ">", "<=", ">="))


def classify_quantifier_var(var: str, body_window: str) -> str:
    """Heuristically classify a quantifier var as index-like or arithmetic-like."""
    if re.search(rf"\[[^\]]*\b{re.escape(var)}\b[^\]]*\]", body_window):
        return "usize"
    if re.search(rf"\b{re.escape(var)}\b[^\n]{{0,40}}<(?:=)?[^\n]{{0,40}}\.len\(\)", body_window):
        return "usize"
    if re.search(rf"\.update\([^,\)]*\b{re.escape(var)}\b", body_window):
        return "usize"
    if re.search(rf"\.subrange\([^,\)]*\b{re.escape(var)}\b", body_window):
        return "usize"
    if re.search(rf"\.(?:take|skip)\(\s*\b{re.escape(var)}\b", body_window):
        return "usize"
    return "i64"


SPEC_FN_ANY_RE = re.compile(r"(?:pub\s+open\s+)?spec\s+fn\s+(\w+)")


def is_word_at(text: str, pos: int, word: str) -> bool:
    if not text.startswith(word, pos):
        return False
    before_ok = pos == 0 or not (text[pos - 1].isalnum() or text[pos - 1] == "_")
    end = pos + len(word)
    after_ok = end == len(text) or not (text[end].isalnum() or text[end] == "_")
    return before_ok and after_ok


def wrap_block_as_i64(inner: str) -> str:
    if not inner.strip():
        return inner
    indent = "    "
    for line in inner.splitlines():
        if line.strip():
            indent = re.match(r"\s*", line).group(0)
            break
    body = inner.strip("\n")
    return f"\n{indent}({{\n{body}\n{indent}}}) as i64\n"


def wrap_i64_if_else_blocks(body: str) -> str:
    """Wrap branch blocks inside i64-returning helper bodies."""

    def rec(segment: str) -> str:
        out: list[str] = []
        i = 0
        while i < len(segment):
            if is_word_at(segment, i, "if"):
                j = i + 2
                depth = 0
                while j < len(segment):
                    ch = segment[j]
                    if ch in "([":
                        depth += 1
                    elif ch in ")]":
                        depth -= 1
                    elif ch == "{" and depth == 0:
                        break
                    j += 1
                if j >= len(segment):
                    out.append(segment[i:])
                    break

                then_open = j
                then_close = find_matching_brace(segment, then_open)
                if then_close == -1:
                    out.append(segment[i:])
                    break

                then_inner = rec(segment[then_open + 1 : then_close])
                out.append(segment[i : then_open + 1])
                out.append(wrap_block_as_i64(then_inner))
                out.append("}")
                i = then_close + 1

                ws_start = i
                while i < len(segment) and segment[i].isspace():
                    i += 1
                out.append(segment[ws_start:i])

                if is_word_at(segment, i, "else"):
                    out.append("else")
                    i += 4
                    ws_start = i
                    while i < len(segment) and segment[i].isspace():
                        i += 1
                    out.append(segment[ws_start:i])
                    if is_word_at(segment, i, "if"):
                        continue
                    if i < len(segment) and segment[i] == "{":
                        else_open = i
                        else_close = find_matching_brace(segment, else_open)
                        if else_close == -1:
                            out.append(segment[i:])
                            break
                        else_inner = rec(segment[else_open + 1 : else_close])
                        out.append("{")
                        out.append(wrap_block_as_i64(else_inner))
                        out.append("}")
                        i = else_close + 1
                continue

            out.append(segment[i])
            i += 1

        return "".join(out)

    return body[0] + rec(body[1:-1]) + body[-1]


def wrap_i64_return_body(body: str) -> str:
    inner = body[1:-1].strip("\n")
    if not inner.strip():
        return body
    indented = "\n".join(
        ("        " + line) if line.strip() else ""
        for line in inner.splitlines()
    )
    return "{\n    ({\n" + indented + "\n    }) as i64\n}"


def find_matching_paren(text: str, start: int) -> int:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return i
    return -1


def extract_param_types_from_header(header: str) -> list[str]:
    open_paren = header.find("(")
    if open_paren == -1:
        return []
    close_paren = find_matching_paren(header, open_paren)
    if close_paren == -1:
        return []
    args_raw = header[open_paren + 1 : close_paren].strip()
    if not args_raw:
        return []
    param_types: list[str] = []
    for part in split_top_level(args_raw):
        if ":" not in part:
            continue
        _, typ = part.split(":", 1)
        param_types.append(typ.strip())
    return param_types


def rewrite_spec_fn_int_types(
    text: str,
) -> tuple[str, dict[str, list[str]], dict[str, str]]:
    """Lower helper `spec fn` integer signatures from Verus ints to Rust ints.

    `exec_spec_unverified!` rejects `int`/`nat` in type position.  This pass
    rewrites helper signatures first, records the rewritten parameter/return
    types, and then later passes use that metadata to insert casts at call sites
    and comparisons.
    """
    out: list[str] = []
    fn_param_types: dict[str, list[str]] = {}
    fn_return_types: dict[str, str] = {}
    pos = 0
    for m in SPEC_FN_ANY_RE.finditer(text):
        body_open, body_close = find_fn_body_brace(text, m.end())
        if body_open == -1 or body_close == -1:
            continue
        out.append(text[pos : m.start()])
        fn_name = m.group(1)
        header = text[m.start() : body_open]
        body = text[body_open : body_close + 1]

        header = re.sub(
            r"(\w+)\s*:\s*(int|nat)\b",
            lambda mm: f"{mm.group(1)}: i64",
            header,
        )

        ret_seq_match = re.search(r"->\s*Seq<\s*([^>]+)\s*>", header)
        if ret_seq_match:
            elem_ty = ret_seq_match.group(1).strip()
            body = body.replace("seq![]", f"Seq::<{elem_ty}>::empty()")

        if re.search(r"->\s*(int|nat)\b", header):
            header = re.sub(r"->\s*(int|nat)\b", "-> i64", header)
            body = wrap_i64_if_else_blocks(body)
            body = wrap_i64_return_body(body)

        fn_param_types[fn_name] = extract_param_types_from_header(header)
        ret_m = re.search(r"->\s*([^\s\{]+)", header)
        if ret_m:
            fn_return_types[fn_name] = ret_m.group(1).strip()
        out.append(header + body)
        pos = body_close + 1
    out.append(text[pos:])
    return "".join(out), fn_param_types, fn_return_types


def rewrite_exec_usize_arg(expr: str) -> str:
    expr = expr.strip()
    for cast_ty in ("i64", "u64", "int", "nat"):
        m = re.fullmatch(rf"(.+?)\s+as\s+{cast_ty}", expr)
        if m:
            expr = m.group(1).strip()
            break
    if re.fullmatch(r".+\bas\s+usize\b", expr):
        return expr
    if expr.endswith(".len()"):
        return f"({expr}) as usize"
    return f"({expr}) as usize"


def rewrite_exec_i64_arg(expr: str) -> str:
    expr = expr.strip()
    for cast_ty in ("int", "nat"):
        m = re.fullmatch(rf"(.+?)\s+as\s+{cast_ty}", expr)
        if m:
            expr = m.group(1).strip()
            break
    if re.fullmatch(r".+\bas\s+i64\b", expr):
        return expr
    return f"({expr}) as i64"


def rewrite_spec_fn_calls(text: str, fn_param_types: dict[str, list[str]]) -> str:
    """Push integer casts into helper call arguments after signature lowering."""
    out: list[str] = []
    i = 0
    while i < len(text):
        if text[i].isalpha() or text[i] == "_":
            j = i + 1
            while j < len(text) and (text[j].isalnum() or text[j] == "_"):
                j += 1
            name = text[i:j]
            if name in fn_param_types:
                k = j
                while k < len(text) and text[k].isspace():
                    k += 1
                if k < len(text) and text[k] == "(":
                    prev = text[:i].rstrip()
                    if not prev.endswith("fn"):
                        end = find_matching_paren(text, k)
                        if end != -1:
                            args_raw = text[k + 1 : end]
                            args = split_top_level(args_raw)
                            param_types = fn_param_types[name]
                            rewritten_args: list[str] = []
                            for idx, arg in enumerate(args):
                                arg = rewrite_spec_fn_calls(arg.strip(), fn_param_types)
                                if idx < len(param_types) and param_types[idx] == "usize":
                                    rewritten_args.append(rewrite_exec_usize_arg(arg))
                                elif idx < len(param_types) and param_types[idx] == "i64":
                                    rewritten_args.append(rewrite_exec_i64_arg(arg))
                                else:
                                    rewritten_args.append(arg.strip())
                            out.append(f"{name}(" + ", ".join(rewritten_args) + ")")
                            i = end + 1
                            continue
            out.append(text[i:j])
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def line_mentions_i64_fn(line: str, i64_fn_names: set[str]) -> bool:
    return any(re.search(rf"\b{re.escape(name)}\s*\(", line) for name in i64_fn_names)


def rewrite_nonnegative_i64_comparisons(line: str, i64_fn_names: set[str]) -> str:
    if line.strip().endswith(("&&", "||")):
        return line
    parts = split_top_level_op(line, "&&")
    if len(parts) <= 1:
        return line

    nonnegative_keys: set[str] = set()
    changed = False
    for part in parts:
        candidate = strip_balanced_parens(part)
        m = re.fullmatch(r"0\s*<=\s*(.+)", candidate)
        if m:
            nonnegative_keys.add(strip_trigger_prefix(strip_balanced_parens(m.group(1))))

    rewritten: list[str] = []
    for part in parts:
        candidate = strip_balanced_parens(part)
        m = re.fullmatch(r"(.+?)\s*(<=|<)\s*(.+)", candidate)
        if m:
            lhs = m.group(1).strip()
            lhs_key = strip_trigger_prefix(strip_balanced_parens(lhs))
            rhs = m.group(3).strip()
            if lhs_key in nonnegative_keys and line_mentions_i64_fn(rhs, i64_fn_names):
                cmp = f"(({lhs}) as i64) {m.group(2)} {rhs}"
                if part.strip().startswith("(") and part.strip().endswith(")"):
                    part = f"({cmp})"
                else:
                    part = cmp
                changed = True
        rewritten.append(part.strip())
    if changed:
        return " && ".join(rewritten)
    return line


def rewrite_i64_quantifier_line(line: str, i64_fn_names: set[str]) -> str:
    m = re.search(r"\b(forall|exists)\s*\|([^|]+)\|\s*(.+)", line)
    if not m:
        return line
    kind = m.group(1)
    binders = [p.strip() for p in split_top_level(m.group(2)) if p.strip()]
    if len(binders) != 1:
        return line
    if ":" not in binders[0]:
        return line
    var, ty = [p.strip() for p in binders[0].split(":", 1)]
    if ty != "i64":
        return line

    body = m.group(3).strip()
    if kind == "forall":
        split = split_once_top_level(body, "==>")
        if split is None:
            return line
        antecedent, consequent = split
        guard = antecedent.strip()
        tail = f" ==> {consequent.strip()}"
    else:
        parts = split_top_level_op(body, "&&")
        if len(parts) < 2:
            return line
        guard = parts[0].strip()
        tail = " && " + " && ".join(p.strip() for p in parts[1:])

    gm = re.match(
        rf"^\s*(?P<lower>.+?)\s*(?P<op1><=|<)\s*{re.escape(var)}\s*"
        rf"(?P<op2><=|<)\s*(?P<upper>.+?)\s*$",
        guard,
        re.DOTALL,
    )
    if gm is None or not line_mentions_i64_fn(gm.group("upper"), i64_fn_names):
        return line
    lower = gm.group("lower").strip()
    if "as i64" in lower:
        return line
    new_guard = (
        f"(({lower}) as i64) {gm.group('op1')} {var} "
        f"{gm.group('op2')} {gm.group('upper').strip()}"
    )
    return line[: m.start(3)] + new_guard + tail


def rewrite_i64_fn_binary_comparisons(line: str, i64_fn_names: set[str]) -> str:
    if not i64_fn_names:
        return line
    if not line_mentions_i64_fn(line, i64_fn_names):
        return line

    indent = re.match(r"\s*", line).group(0)
    candidate = line.strip()
    wrapped = False
    inner = strip_balanced_parens(candidate)
    if inner != candidate:
        wrapped = True
        candidate = inner

    m = re.match(
        r"^(?P<lhs>[A-Za-z_]\w*(?:\s+as\s+[A-Za-z_][A-Za-z0-9_]*)?)\s*"
        r"(?P<op>==|!=|<=|<|>=|>)\s*(?P<rhs>.+)$",
        candidate,
    )
    if not m:
        return line
    lhs = m.group("lhs").strip()
    rhs = m.group("rhs").strip()
    if lhs.endswith("as i64") or lhs in {"true", "false"}:
        return line
    if not line_mentions_i64_fn(rhs, i64_fn_names):
        return line
    rewritten = f"({lhs} as i64) {m.group('op')} {rhs}"
    if wrapped:
        rewritten = f"({rewritten})"
    return indent + rewritten


def rewrite_i64_comparisons_in_text(text: str, i64_fn_names: set[str]) -> str:
    """Repair mixed-width comparisons introduced by `int` -> `i64` lowering."""
    if not i64_fn_names:
        return text
    lines: list[str] = []
    for line in text.splitlines():
        if "forall" in line or "exists" in line:
            line = rewrite_i64_quantifier_line(line, i64_fn_names)
        line = rewrite_i64_fn_binary_comparisons(line, i64_fn_names)
        line = rewrite_nonnegative_i64_comparisons(line, i64_fn_names)
        lines.append(line)
    return "\n".join(lines)


def protect_exec_indices(text: str) -> tuple[str, list[str]]:
    """Replace actual indexing brackets with placeholders."""
    out: list[str] = []
    parts: list[str] = []
    i = 0
    while i < len(text):
        if text[i] == "[" and (i == 0 or text[i - 1] not in "#!"):
            depth = 1
            j = i + 1
            while j < len(text):
                if text[j] == "[" and text[j - 1] not in "#!":
                    depth += 1
                elif text[j] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= len(text):
                out.append(text[i:])
                break
            key = f"__IDXSEG_{len(parts)}__"
            parts.append(text[i : j + 1])
            out.append(key)
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out), parts


def restore_exec_indices(text: str, parts: list[str]) -> str:
    for i, seg in enumerate(parts):
        text = text.replace(f"__IDXSEG_{i}__", seg)
    return text


def rewrite_index_expr(expr: str, quant_vars: set[str]) -> str:
    expr = expr.strip()
    if re.fullmatch(r"\d+", expr):
        return expr
    if re.fullmatch(r".+\bas\s+usize\s+as\s+int", expr):
        return expr
    cast_match = re.fullmatch(r"(.+?)\s+as\s+(int|nat)", expr)
    if cast_match:
        inner = cast_match.group(1).strip()
        if inner in quant_vars:
            return f"{inner} as int"
        return f"({inner} as usize) as int"
    return f"({expr}) as usize as int"


def rewrite_exec_indices(text: str, quant_vars: set[str]) -> str:
    """Wrap non-usize index expressions so exec code type-checks."""

    def rec(segment: str) -> str:
        out: list[str] = []
        i = 0
        while i < len(segment):
            if segment[i] == "[" and (i == 0 or segment[i - 1] not in "#!"):
                depth = 1
                j = i + 1
                while j < len(segment):
                    if segment[j] == "[" and segment[j - 1] not in "#!":
                        depth += 1
                    elif segment[j] == "]":
                        depth -= 1
                        if depth == 0:
                            break
                    j += 1
                if j >= len(segment):
                    out.append(segment[i:])
                    break
                inner = rec(segment[i + 1 : j])
                out.append("[" + rewrite_index_expr(inner, quant_vars) + "]")
                i = j + 1
            else:
                out.append(segment[i])
                i += 1
        return "".join(out)

    return rec(text)


def rewrite_seq_method_arg(expr: str, quant_vars: set[str]) -> str:
    expr = expr.strip()
    m = re.fullmatch(r"(.+?)\s+as\s+i64", expr)
    if m:
        expr = m.group(1).strip()
    return rewrite_index_expr(expr, quant_vars)


def cast_exec_method_args(text: str, quant_vars: set[str]) -> str:
    """Cast Seq method index/count args so raw spec uses `int` and exec uses `usize`."""
    text = re.sub(
        r"\.update\(\s*([^,]+?)\s*,",
        lambda m: f".update({rewrite_seq_method_arg(m.group(1), quant_vars)},",
        text,
    )
    text = re.sub(
        r"\.(take|skip)\(\s*([^)]+?)\s*\)",
        lambda m: f".{m.group(1)}({rewrite_seq_method_arg(m.group(2), quant_vars)})",
        text,
    )
    text = re.sub(
        r"\.subrange\(\s*([^,]+?)\s*,\s*([^)]+?)\s*\)",
        lambda m: (
            f".subrange({rewrite_seq_method_arg(m.group(1), quant_vars)}, "
            f"{rewrite_seq_method_arg(m.group(2), quant_vars)})"
        ),
        text,
    )
    return text


# ---------------------------------------------------------------------------
# Transitive spec-fn dependency resolution
# ---------------------------------------------------------------------------


def find_needed_spec_fns(
    clauses: list[str],
    all_fns: dict[str, str],
) -> list[str]:
    """Compute the transitive closure of helper spec functions.

    We start from names mentioned directly in the postcondition, then keep
    pulling in helpers referenced by those helpers until the set stabilizes.
    Order is preserved by returning names in their original source order.
    """
    needed: set[str] = set()
    queue: set[str] = set()

    text = "\n".join(clauses)
    for name in all_fns:
        if re.search(rf"\b{re.escape(name)}\b", text):
            queue.add(name)

    while queue:
        name = queue.pop()
        if name in needed:
            continue
        needed.add(name)
        fn_text = all_fns[name]
        for other in all_fns:
            if other not in needed and re.search(
                rf"\b{re.escape(other)}\b", fn_text
            ):
                queue.add(other)

    return [n for n in all_fns if n in needed]


# ---------------------------------------------------------------------------
# Blockers: constructs the macro cannot compile
# ---------------------------------------------------------------------------

# Seq::new has no exec equivalent
HARD_BLOCKERS_RE = re.compile(r"\bSeq::new\b")
PRIMITIVE_QUANT_TYPES = {
    "bool",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "usize",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "isize",
    "char",
    "int",
    "nat",
}


def detect_blockers(spec_fn_text: str) -> list[str]:
    """Return human-readable blockers found in *spec_fn_text*."""
    blockers: list[str] = []
    if HARD_BLOCKERS_RE.search(spec_fn_text):
        blockers.append("Seq::new (no exec equivalent)")
    for m in re.finditer(r"\b(?:forall|exists)\s*\|([^|]+)\|", spec_fn_text):
        for part in split_top_level(m.group(1)):
            if ":" not in part:
                continue
            _, typ = part.split(":", 1)
            typ = typ.strip()
            if typ not in PRIMITIVE_QUANT_TYPES:
                blockers.append(
                    f"quantifier over unsupported type `{typ}`"
                )
                return blockers
    return blockers


def is_supported_quantifier_guard(part: str, var: str) -> bool:
    part = strip_trigger_prefix(strip_balanced_parens(part))
    return (
        re.fullmatch(
            rf".+?(?:<=|<)\s*{re.escape(var)}\s*(?:<=|<)\s*.+",
            part,
            re.DOTALL,
        )
        is not None
    )


def detect_transformed_blockers(text: str) -> list[str]:
    blockers = detect_blockers(text)
    if blockers:
        return blockers
    if "old(" in text:
        return ["old(...) state references not supported"]
    return []


def builtin_exec_math_specs(text: str, existing_spec_fn_names: set[str]) -> list[str]:
    """Synthesize tiny executable specs for helpers commonly imported in Verus.

    Some benchmarks call spec helpers such as `pow2`, `pow`, or `log` through
    imports.  The macro only sees the local block we hand it, so we materialize a
    small fallback definition when the benchmark references one of these names
    but does not define it locally.
    """
    helpers: list[str] = []
    if re.search(r"\bpow2\s*\(", text) and "pow2" not in existing_spec_fn_names:
        helpers.append(
            """spec fn pow2(n: i64) -> i64
    decreases n,
{
    ({ if n <= 0 { 1 } else { 2 * pow2((n - 1) as i64) } }) as i64
}"""
        )
    if re.search(r"\bpow\s*\(", text) and "pow" not in existing_spec_fn_names:
        helpers.append(
            """spec fn pow(base: i64, exp: i64) -> i64
    decreases exp,
{
    ({ if exp <= 0 { 1 } else { base * pow((base) as i64, (exp - 1) as i64) } }) as i64
}"""
        )
    if re.search(r"\blog\s*\(", text) and "log" not in existing_spec_fn_names:
        helpers.append(
            """spec fn log(base: i64, x: i64) -> i64
    decreases x,
{
    ({ if base <= 1i64 || x < base { 0 } else { 1 + log((base) as i64, (x / base) as i64) } }) as i64
}"""
        )
    if re.search(r"\bspec_min\s*\(", text) and "spec_min" not in existing_spec_fn_names:
        helpers.append(
            """spec fn spec_min(a: i64, b: i64) -> i64 {
    if a <= b { a } else { b }
}"""
        )
    if re.search(r"\bspec_max\s*\(", text) and "spec_max" not in existing_spec_fn_names:
        helpers.append(
            """spec fn spec_max(a: i64, b: i64) -> i64 {
    if a >= b { a } else { b }
}"""
        )
    return helpers


# ---------------------------------------------------------------------------
# exec_spec_unverified! transformation
# ---------------------------------------------------------------------------
#
# Rules applied (derived from reading the proc-macro source):
#
#   Syntax / types
#   - `pub open spec fn` -> `spec fn`
#   - `Self::` removed  (standalone spec fns, not inside impl)
#   - `Vec<T>` -> `Seq<T>` in type positions (macro maps Seq->Vec/&[T])
#   - `@` (view) stripped  (macro passes through; our params are already spec types)
#
#   int / nat are NOT valid types inside the macro (for params,
#   quantifier vars, return types).  They must be replaced with
#   a concrete Rust integer type.
#   - quantifier vars  `|x: int|`  -> `|x: usize|`
#   - fn params        `n: int`    -> `n: usize`
#   - return types     `-> int`    -> `-> usize`
#   `as int` / `as nat` casts are kept; the macro strips them.
#
#   After changing a variable from `int` to `usize`, Seq indexing
#   (`seq[var]`) still needs `as int` for the verus-syn parser:
#   `seq[var]` -> `seq[var as int]`.
#
#   Supported quantifier forms (exec_spec_unverified!):
#     forall |x1: T, ..., xN: T| guard1 && ... && guardN ==> body
#     exists |x1: T, ..., xN: T| guard1 && ... && guardN && body
#   where each guard is:  lower </<= x </<= upper
#   and types must be concrete Rust integers (u8..u128, i8..i128,
#   usize, isize, char).
#
#   Supported type mappings:
#     Seq<T> -> Vec<T> (owned) / &[T] (ref)
#     Map<K,V> -> HashMap<K,V>
#     Set<T> -> HashSet<T>
#     Option<T> -> Option<T>
#     primitives stay as-is
#     `int`, `nat`, `Vec`, `String`, `str` are ERRORS in type position
#
#   Supported operations:
#     Seq indexing, .len(), .subrange(), .add(), ==, Seq::empty()
#     if/else (else required), let, match, arithmetic, &&, ||,
#     ==>, <==, <==> (compiled to boolean ops),
#     function calls (prefixed with exec_),
#     `as int`/`as nat` stripped, other casts preserved
#     `@` (view) stripped
#     `&&&` / `|||` (BigAnd/BigOr) supported
#     `#[trigger]` kept (no-op in exec)
#
#   NOT supported / hard blockers:
#     Seq::new (no exec equivalent)
#     `int`/`nat` as types (must convert to concrete type)


def transform_for_exec_spec(text: str) -> str:
    """Apply the full text-level lowering pipeline for `exec_spec_unverified!`.

    The order matters:
    - rewrite helper signatures first so later passes know the concrete types;
    - simplify Verus-only surface syntax into Rust-like syntax;
    - fix casts/indexing after integer lowering;
    - finally strip the remaining syntax that the macro treats as decoration.
    """

    text, fn_param_types, fn_return_types = rewrite_spec_fn_int_types(text)
    text = normalize_big_boolean_blocks(text)

    # 1. pub open spec fn -> spec fn
    text = re.sub(r"pub\s+open\s+spec\s+fn", "spec fn", text)
    text = re.sub(r"pub\s+const\b", "const", text)

    # 2. Remove Self:: and Solution:: prefixes
    text = text.replace("Self::", "")
    text = re.sub(r"\bSolution::", "", text)

    # 3. Vec<T> -> Seq<T>  (macro maps Seq back to Vec/&[T] in exec)
    text = re.sub(r"\bVec<", "Seq<", text)

    # 3b. Strings must use the exec-spec alias rather than Rust's String type.
    text = re.sub(r"\bString\b", "SpecString", text)

    # 4. Strip Verus view operators.
    text = text.replace("@", "")

    # 4b. Convert integer literals with `int`/`nat` suffix: 0int -> 0i64, 1nat -> 1u64
    #     These are Verus-specific suffixes not valid in Rust.
    text = re.sub(r"\b(\d[\d_]*)int\b", r"\1i64", text)
    text = re.sub(r"\b(\d[\d_]*)nat\b", r"\1u64", text)

    # 5. Quantifier variables become signed exec integers.
    #    We standardize on `i64` here because many specs mix arithmetic with
    #    values that are naturally signed once they leave pure Verus land.
    quant_index_vars: set[str] = set()

    def replace_quantifier_binders(m: re.Match[str]) -> str:
        binders = m.group(1)
        parts: list[str] = []
        for part in split_top_level(binders):
            part = part.strip()
            vm = re.match(r"(\w+)\s*:\s*(int|nat)\b", part)
            if vm:
                var = vm.group(1)
                parts.append(f"{var}: i64")
            else:
                parts.append(part)
        return "|" + ", ".join(parts) + "|"

    text = re.sub(r"\|([^|]+)\|", replace_quantifier_binders, text)

    # 6. All remaining Verus ints in type positions become signed exec ints.
    text = re.sub(
        r"(\w+)\s*:\s*\b(int|nat)\b",
        lambda m: f"{m.group(1)}: i64" if m.group(1) != "as" else m.group(0),
        text,
    )
    text = re.sub(r"->\s*(int|nat)\b", "-> i64", text)
    text = re.sub(r"\bSeq<\s*int\s*>", "Seq<i64>", text)
    text = re.sub(r"\bSeq<\s*nat\s*>", "Seq<i64>", text)
    text = re.sub(r"\bSet<\s*int\s*>", "Set<i64>", text)
    text = re.sub(r"\bSet<\s*nat\s*>", "Set<i64>", text)
    text = re.sub(r"\bOption<\s*int\s*>", "Option<i64>", text)
    text = re.sub(r"\bOption<\s*nat\s*>", "Option<i64>", text)
    text = text.replace("=~=", "==")

    # 7. Preserve signed intent for casts, but keep exec indexing on usize.
    #    This is the awkward part of the lowering: helper arithmetic wants
    #    `i64`, but concrete Rust indexing still wants `usize`.
    text = re.sub(r"\.len\(\)\s+as\s+(int|nat)\b", ".len() as i64", text)
    protected_len, idx_parts = protect_exec_indices(text)
    protected_len = re.sub(r"\.len\(\)(?!\s+as\b)", ".len() as i64", protected_len)
    text = restore_exec_indices(protected_len, idx_parts)
    text = rewrite_spec_fn_calls(text, fn_param_types)
    i64_fn_names = {
        name for name, ret in fn_return_types.items() if ret == "i64"
    }
    text = rewrite_i64_comparisons_in_text(text, i64_fn_names)
    text = rewrite_exec_indices(text, quant_index_vars)
    protected, idx_parts = protect_exec_indices(text)
    protected = re.sub(r"\bas\s+(int|nat)\b", "as i64", protected)
    text = restore_exec_indices(protected, idx_parts)
    text = cast_exec_method_args(text, quant_index_vars)
    text = re.sub(r"\blet\s+(\w+)\s*:\s*([^=;]+?)\s*=", r"let \1 =", text)
    text = text.replace("&&&", "&&").replace("|||", "||")

    return text


def fresh_identifier(base: str, forbidden: set[str]) -> str:
    candidate = base
    if candidate not in forbidden:
        return candidate
    suffixes = ("_ret", "_out", "_result")
    for suffix in suffixes:
        candidate = f"{base}{suffix}"
        if candidate not in forbidden:
            return candidate
    i = 2
    while True:
        candidate = f"{base}_ret{i}"
        if candidate not in forbidden:
            return candidate
        i += 1


def sanitize_reserved_param_names(fn_text: str) -> str:
    """Rename helper params that collide with Verus's implicit `res` return name."""
    header_end = fn_text.find("{")
    if header_end == -1:
        header_end = len(fn_text)
    header = fn_text[:header_end]
    param_names = {
        m.group(1)
        for m in re.finditer(r"\b(\w+)\s*:\s*([^,\)\n]+)", header)
    }
    forbidden = {"res"}
    for name in sorted(param_names & forbidden):
        fresh = fresh_identifier(name, param_names | forbidden)
        fn_text = re.sub(rf"\b{re.escape(name)}\b", fresh, fn_text)
        param_names.discard(name)
        param_names.add(fresh)
    return fn_text


# ---------------------------------------------------------------------------
# Render test_post.rs
# ---------------------------------------------------------------------------


def dedent_block(text: str) -> str:
    """Remove common leading whitespace from a multi-line block.

    Ignores the first line when computing indent (it may start mid-line
    after regex extraction).
    """
    lines = text.split("\n")
    if len(lines) <= 1:
        return text.strip()
    min_indent = None
    for line in lines[1:]:
        stripped = line.lstrip(" ")
        if stripped:
            indent = len(line) - len(stripped)
            if min_indent is None or indent < min_indent:
                min_indent = indent
    if min_indent and min_indent > 0:
        result = [lines[0].strip()]
        for line in lines[1:]:
            result.append(line[min_indent:] if len(line) >= min_indent else line)
        return "\n".join(result)
    return text


def render_test_post_rs(
    method_name: str,
    sig: Signature,
    needed_fn_names: list[str],
    all_fns: dict[str, str],
    ensures_clauses: list[str],
    extra_use_lines: list[str] | None = None,
    extra_const_lines: list[str] | None = None,
) -> str:
    """Produce the full ``test_post.rs`` file content."""

    # Assemble the raw spec block in source order first.  This keeps the block
    # human-readable and makes later blocker/error reports line up better with
    # the original helpers.
    parts: list[str] = []
    for name in needed_fn_names:
        helper_text = dedent_block(all_fns[name])
        helper_text = sanitize_reserved_param_names(helper_text)
        helper_text = normalize_quantifiers_in_text(helper_text)
        parts.append(helper_text)

    # Use the named return variable from the signature (e.g. `res` in `(res: Type)`)
    ret_var, ret_type = parse_return(sig.ret)
    arg_names = {n for n, _ in sig.args}
    rendered_ret_var = fresh_identifier(ret_var, arg_names | {"res"})

    if rendered_ret_var != ret_var:
        ensures_clauses = [
            re.sub(rf"\b{re.escape(ret_var)}\b", rendered_ret_var, clause)
            for clause in ensures_clauses
        ]

    # Parameters = original fn params + the return variable
    params: list[str] = []
    for n, t in sig.args:
        params.append(f"    {n}: {t}")
    params.append(f"    {rendered_ret_var}: {ret_type}")
    params_str = ",\n".join(params)

    body_lines: list[str] = []
    for i, clause in enumerate(ensures_clauses):
        clause = normalize_quantifiers_in_clause(clause)
        if "forall" not in clause and "exists" not in clause:
            clause = normalize_simple_chain(clause)
        prefix = "    " if i == 0 else "    && "
        body_lines.append(f"{prefix}({clause})")
    body = "\n".join(body_lines)

    parts.append(
        f"pub open spec fn {method_name}_postcondition(\n"
        f"{params_str},\n"
        f") -> bool {{\n"
        f"{body}\n"
        f"}}"
    )

    # Builtin helper synthesis depends on the raw, pre-lowered names that appear
    # in the assembled spec block.
    raw_block_preview = "\n\n".join(parts)
    builtin_specs = builtin_exec_math_specs(raw_block_preview, set(all_fns))
    builtin_names = {
        re.search(r"spec fn\s+(\w+)", spec).group(1)
        for spec in builtin_specs
        if re.search(r"spec fn\s+(\w+)", spec)
    }
    if builtin_specs:
        parts = builtin_specs + parts

    raw_block = "\n\n".join(parts)
    transformed = transform_for_exec_spec(raw_block)
    import_lines = [
        "use vstd::contrib::exec_spec::*;",
        "use vstd::prelude::*;",
    ]
    for line in extra_use_lines or []:
        if line not in import_lines:
            import_lines.append(line)
    # If we synthesized a local helper, drop imports that would shadow it.
    if "pow2" in builtin_names:
        import_lines = [
            line for line in import_lines if "power2::pow2" not in line
        ]
    if "pow" in builtin_names:
        import_lines = [
            line for line in import_lines if "power::pow" not in line
        ]
    if "log" in builtin_names:
        import_lines = [
            line for line in import_lines if "logarithm::log" not in line
        ]
    imports = "\n".join(import_lines)
    const_lines = "\n".join(extra_const_lines or [])
    const_block = f"{const_lines}\n\n" if const_lines else ""

    return (
        f"{imports}\n"
        "\n"
        "verus! {\n"
        "\n"
        f"{const_block}"
        "exec_spec_unverified! {\n"
        "\n"
        f"{transformed}\n"
        "\n"
        "}\n"
        "\n"
        "}\n"
        "\n"
        "fn main() {}\n"
    )


def find_verus_binary() -> str | None:
    env_verus = os.environ.get("VERUS")
    if env_verus and Path(env_verus).exists():
        return env_verus

    repo_verus = REPO_ROOT / "verus" / "verus"
    if repo_verus.exists():
        return str(repo_verus)

    return shutil.which("verus")


def compile_test_post(target: Path, verus_bin: str) -> tuple[str, str]:
    result = subprocess.run(
        [verus_bin, "--compile", str(target)],
        capture_output=True,
        text=True,
        timeout=120,
    )
    if result.returncode != 0:
        err = (result.stderr or result.stdout).strip()
        return "compile_error", err[:2000]
    return "compiled", str(target)


# ---------------------------------------------------------------------------
# Per-problem driver
# ---------------------------------------------------------------------------


@dataclass
class Result:
    problem: Path
    status: str
    detail: str = ""
    blockers: list[str] = field(default_factory=list)


def scaffold_one(
    problem_dir: Path,
    force: bool,
    do_compile: bool = False,
    verus_bin: str | None = None,
) -> Result:
    spec_rs = problem_dir / "spec.rs"
    if not spec_rs.exists():
        spec_rs = problem_dir / "code_spec.rs"
    if not spec_rs.exists():
        return Result(problem_dir, "skipped_no_spec")

    tests_dir = problem_dir / "tests"
    target = tests_dir / "test_post.rs"
    if target.exists() and not force:
        if do_compile and verus_bin:
            status, detail = compile_test_post(target, verus_bin)
            return Result(problem_dir, status, detail)
        return Result(problem_dir, "skipped_existing", str(target))

    try:
        spec_text = spec_rs.read_text()
        verus_text = extract_verus_block(spec_text)
        if not verus_text:
            return Result(problem_dir, "error", "no verus! block")

        # Collect spec fns from the entire verus block (inside + outside impl)
        all_fns = extract_spec_fns(verus_text)
        fn_name, ensures, returns_expr = choose_target_fn(verus_text)

        if fn_name is None:
            try:
                parse_signature(spec_text)
            except ValueError:
                return Result(problem_dir, "error", "no ensured exec fn found")
            return Result(problem_dir, "skipped_no_ensures")
        if not ensures and returns_expr is None:
            return Result(problem_dir, "skipped_no_ensures")

        sig = parse_signature(spec_text, fn_name)
        if sig.receiver is not None:
            return Result(
                problem_dir,
                "skipped_blocker",
                f"method receiver `{sig.receiver}` not supported",
                [f"method receiver `{sig.receiver}` not supported"],
            )
        if sig.ret == "Self":
            return Result(
                problem_dir,
                "skipped_blocker",
                "return type `Self` not supported",
                ["return type `Self` not supported"],
            )

        if returns_expr is not None:
            ret_var, _ = parse_return(sig.ret)
            ensures = [f"{ret_var} == ({returns_expr})"]

        needed = find_needed_spec_fns(ensures, all_fns)

        # Check for obvious hard blockers in the needed spec fns + ensures
        combined = "\n".join(all_fns[n] for n in needed) + "\n" + "\n".join(ensures)
        blockers = detect_blockers(combined)
        if blockers:
            return Result(
                problem_dir,
                "skipped_blocker",
                "; ".join(blockers),
                blockers,
            )

        extra_use_lines = extract_use_lines(spec_text)
        extra_const_lines = extract_const_lines(verus_text)
        content = render_test_post_rs(
            fn_name,
            sig,
            needed,
            all_fns,
            ensures,
            extra_use_lines=extra_use_lines,
            extra_const_lines=extra_const_lines,
        )
        blockers = detect_transformed_blockers(content)
        if blockers:
            return Result(
                problem_dir,
                "skipped_blocker",
                "; ".join(blockers),
                blockers,
            )

        tests_dir.mkdir(parents=True, exist_ok=True)
        target.write_text(content)

        if do_compile and verus_bin:
            status, detail = compile_test_post(target, verus_bin)
            return Result(problem_dir, status, detail)

        return Result(problem_dir, "generated", str(target))
    except Exception as e:
        return Result(problem_dir, "error", str(e))


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def iter_problems(kind: str) -> list[Path]:
    kinds: list[Path] = []
    if kind in ("leetcode", "both"):
        kinds.append(BENCH_ROOT / "leetcode")
    if kind in ("codeforces", "both"):
        kinds.append(BENCH_ROOT / "codeforces")
    out: list[Path] = []
    for root in kinds:
        if not root.exists():
            continue
        for p in sorted(root.iterdir()):
            if p.is_dir() and (p / "spec.rs").exists():
                out.append(p)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--problem", type=Path, help="single problem directory")
    g.add_argument("--all", action="store_true", help="process every problem")
    ap.add_argument(
        "--kind",
        choices=("leetcode", "codeforces", "both"),
        default="both",
    )
    ap.add_argument("--force", action="store_true", help="overwrite existing")
    ap.add_argument(
        "--compile",
        action="store_true",
        help="also compile generated test_post.rs with local verus",
    )
    args = ap.parse_args()

    problems = (
        [args.problem.resolve()] if args.problem else iter_problems(args.kind)
    )
    if not problems:
        print("no problems found", file=sys.stderr)
        return 1

    verus_bin = None
    if args.compile:
        verus_bin = find_verus_binary()
        if verus_bin is None:
            print("could not find `verus` binary; set VERUS or use repo-local ./verus/verus", file=sys.stderr)
            return 1

    counts: dict[str, int] = {}
    detail_lines: list[str] = []
    for p in problems:
        r = scaffold_one(
            p,
            force=args.force,
            do_compile=args.compile,
            verus_bin=verus_bin,
        )
        counts[r.status] = counts.get(r.status, 0) + 1
        if r.status in ("generated", "compiled", "compile_error", "error", "skipped_blocker"):
            detail_lines.append(
                f"[{r.status:17s}] "
                f"{p.relative_to(REPO_ROOT)}  {r.detail}"
            )

    if detail_lines:
        print("\n".join(detail_lines))
    print()
    print("Summary:")
    for k in (
        "generated",
        "compiled",
        "compile_error",
        "skipped_existing",
        "skipped_blocker",
        "skipped_no_ensures",
        "skipped_no_spec",
        "error",
    ):
        if counts.get(k):
            print(f"  {k:24s} {counts[k]}")

    total = sum(counts.values())
    gen = counts.get("generated", 0) + counts.get("compiled", 0)
    skip_exist = counts.get("skipped_existing", 0)
    convertible = gen + skip_exist
    print(f"\n  convertible: {convertible}/{total} ({100*convertible/total:.1f}%)")

    return 0 if counts.get("error", 0) == 0 and counts.get("compile_error", 0) == 0 else 2


if __name__ == "__main__":
    sys.exit(main())

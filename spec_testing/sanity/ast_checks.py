"""Static sanity checks S1-S7. No Verus; whole dataset in seconds.

Each check emits zero or more flags with the offending clause text for triage.
Clauses are tokenized (never raw substring matched) to avoid `res` matching
`result`.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

from spec_testing.common.specmodel import SpecModel
from spec_testing.common import specmodel as _sm  # ensures post2exe on sys.path
import gen_test_post as gtp  # noqa: E402

_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|::|[<>=!&|+\-*/%@\[\](){},.;#]")
_WRAP_RE = re.compile(r"\b(old|final)\s*\(")


@dataclass
class Flag:
    check: str          # S1..S7
    severity: str       # FLAG_HIGH|FLAG_MED|FLAG_LOW
    message: str
    clause: str = ""


def _tokens(text: str) -> list[str]:
    return _TOKEN_RE.findall(text)


def _idents(text: str) -> set[str]:
    return {t for t in _tokens(text) if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", t)}


def _clause_mentions(clause: str, name: str) -> bool:
    return name in _idents(clause)


def _helper_takes_param(model: SpecModel) -> set[str]:
    """Helper spec fns that (transitively) take at least one parameter."""
    out: set[str] = set()
    for name, text in model.helper_spec_fns.items():
        m = re.search(rf"\bfn\s+{re.escape(name)}\s*\(([^)]*)\)", text)
        if m and m.group(1).strip():
            out.add(name)
    return out


def _unit_return(model: SpecModel) -> bool:
    rt = model.ret_type.strip()
    return rt in ("()", "", "unit")


def check_s1_result_unconstrained(model: SpecModel) -> list[Flag]:
    if model.returns_expr is not None:
        return []
    ret = model.ret_name
    if not model.ensures:
        return []
    if any(_clause_mentions(c, ret) for c in model.ensures):
        return []
    # Void/unit-return functions have no meaningful result; for &mut problems the
    # spec constrains the post-state, not a return value -> not a weakness.
    if _unit_return(model):
        if model.has_mut_ref and any(
            (p.is_mut_ref and _clause_mentions(c, p.name)) for c in model.ensures for p in model.params
        ):
            return []
        if _unit_return(model):
            return []
    return [Flag("S1", "FLAG_HIGH", f"no ensures clause mentions result `{ret}`")]


def check_s2_input_independent(model: SpecModel) -> list[Flag]:
    if not model.ensures:
        return []
    param_names = {p.name for p in model.params}
    helper_with_param = _helper_takes_param(model)
    for c in model.ensures:
        ids = _idents(c)
        if ids & param_names:
            return []
        if ids & helper_with_param:
            return []
        # old(p)/final(p) wrappers count as input references
        if _WRAP_RE.search(c):
            return []
    return [Flag("S2", "FLAG_HIGH", "no ensures clause references any input")]


def check_s3_trivial(model: SpecModel) -> list[Flag]:
    if model.returns_expr is not None:
        return []
    if not model.ensures:
        return [Flag("S3", "FLAG_HIGH", "empty ensures")]
    if all(re.sub(r"\s+", "", c) == "true" for c in model.ensures):
        return [Flag("S3", "FLAG_HIGH", "all ensures clauses are `true`")]
    return []


def _helper_arity(text: str) -> int:
    m = re.search(gtp.FN_HEAD_RE, text)
    if not m:
        return 0
    cp = gtp.find_matching_paren(text, m.end() - 1)
    if cp == -1:
        return 0
    args = text[m.end():cp].strip()
    return len([a for a in args.split(",") if a.strip()])


def check_s4_stub_helper(model: SpecModel) -> list[Flag]:
    flags: list[Flag] = []
    for name, text in model.helper_spec_fns.items():
        body = _extract_body(text)
        if body is None:
            continue
        if not re.fullmatch(r"(true|false|-?\d+(int|nat)?)", body.strip()):
            continue
        # A constant-returning helper is only a *stub* if it takes parameters
        # (i.e. ignores its inputs). Zero-arg constant fns are named constants
        # (MOD, i32_max, GAME_LEN) and are legitimate.
        if _helper_arity(text) == 0:
            continue
        flags.append(Flag("S4", "FLAG_HIGH", f"helper `{name}` ignores its inputs, constant body `{body.strip()}`", name))
    return flags


def _extract_body(fn_text: str) -> str | None:
    """Return the actual fn body (the LAST top-level brace pair), skipping
    decreases/recommends/ensures clause braces via post2exe's helper."""
    m = re.search(gtp.FN_HEAD_RE, fn_text)
    if not m:
        return None
    close_paren = gtp.find_matching_paren(fn_text, m.end() - 1)
    if close_paren == -1:
        return None
    body_open, body_close = gtp.find_fn_body_brace(fn_text, close_paren + 1)
    if body_open == -1 or body_close == -1:
        return None
    return fn_text[body_open + 1:body_close].strip()


def check_s5_degenerate_quantifier(model: SpecModel) -> list[Flag]:
    flags: list[Flag] = []
    for c in model.ensures:
        # crude: guard bounds like `0 <= i < 0`
        for m in re.finditer(r"(-?\d+)\s*<=?\s*[A-Za-z_]\w*\s*<\s*(-?\d+)", c):
            lo, hi = int(m.group(1)), int(m.group(2))
            if lo >= hi:
                flags.append(Flag("S5", "FLAG_MED", f"degenerate quantifier guard {lo}..{hi}", c))
    return flags


def check_s6_tautology(model: SpecModel) -> list[Flag]:
    flags: list[Flag] = []
    for c in model.ensures:
        norm = re.sub(r"\s+", "", c)
        if re.search(r"(?<!\w)(\w+)==\1(?!\w)", norm) or re.search(r"(?<!\w)(\w+)<=\1(?!\w)", norm):
            flags.append(Flag("S6", "FLAG_LOW", "tautological clause (X==X / X<=X)", c))
    return flags


def check_s7_requires_result(model: SpecModel) -> list[Flag]:
    ret = model.ret_name
    for c in model.requires:
        if _clause_mentions(c, ret):
            return [Flag("S7", "FLAG_MED", f"requires mentions result `{ret}`", c)]
    return []


ALL_CHECKS = [
    check_s1_result_unconstrained,
    check_s2_input_independent,
    check_s3_trivial,
    check_s4_stub_helper,
    check_s5_degenerate_quantifier,
    check_s6_tautology,
    check_s7_requires_result,
]


def run_static(model: SpecModel) -> list[Flag]:
    flags: list[Flag] = []
    for chk in ALL_CHECKS:
        flags.extend(chk(model))
    return flags

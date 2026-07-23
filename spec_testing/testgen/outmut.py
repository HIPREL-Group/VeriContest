"""Typed output mutation — negative-case source #1.

Lahiri FMCAD 2024 operator families + extensions, recursive by type, tagged by
operator family, structurally != original. Category stratification (every
applicable family represented per problem) is enforced by the caller via the
`op` tag on each mutant.
"""
from __future__ import annotations

import copy
import random
from dataclasses import dataclass

from spec_testing.common.values import SpecType, PRIMITIVE_INT, _INT_RANGES  # type: ignore


@dataclass
class Mutant:
    value: object
    op: str              # operator family, e.g. "int_pm", "seq_drop", "bool_flip"


def _structurally_ne(a, b) -> bool:
    return a != b


def _int_type_bounds(rust_name: str) -> tuple[int, int]:
    return _INT_RANGES.get(rust_name, (-(2**31), 2**31 - 1))


def _mutate_int(v: int, st: SpecType, rng: random.Random, primary_len: int) -> list[Mutant]:
    lo, hi = _int_type_bounds(st.rust_name)
    out: list[Mutant] = []
    k = rng.randint(1, 10)
    for cand, op in [
        (v + k, "int_pm"),
        (v - k, "int_pm"),
        (-v, "int_neg"),
        (0, "int_zero"),
        (lo, "int_min"),
        (hi, "int_max"),
        (v + primary_len, "int_off_len"),
        (v - primary_len, "int_off_len"),
    ]:
        if lo <= cand <= hi and cand != v:
            out.append(Mutant(cand, op))
    return out


def _mutate_bool(v: bool) -> list[Mutant]:
    return [Mutant(not v, "bool_flip")]


def _mutate_char(v: str) -> list[Mutant]:
    if not v:
        return []
    o = ord(v[0])
    out = []
    for delta, op in [(1, "char_adj"), (-1, "char_adj")]:
        c = o + delta
        if 32 <= c <= 0x10FFFF:
            out.append(Mutant(chr(c), "char_adj"))
    return out


def _mutate_seq(v: list, st: SpecType, rng: random.Random, primary_len: int) -> list[Mutant]:
    inner = st.inner
    out: list[Mutant] = []
    n = len(v)

    if n > 0:
        # drop element
        i = rng.randrange(n)
        m = v[:i] + v[i + 1:]
        out.append(Mutant(m, "seq_drop"))
        # dup first
        out.append(Mutant([v[0]] + v, "seq_dup_first"))
        # reverse
        if v[::-1] != v:
            out.append(Mutant(v[::-1], "seq_reverse"))
        # truncate half
        if n >= 2:
            out.append(Mutant(v[: n // 2], "seq_trunc"))
        # sort (numeric/char only)
        try:
            s = sorted(v)
            if s != v:
                out.append(Mutant(s, "seq_sort"))
        except TypeError:
            pass
        # swap two indices
        if n >= 2:
            i, j = rng.sample(range(n), 2)
            m = list(v)
            m[i], m[j] = m[j], m[i]
            if m != v:
                out.append(Mutant(m, "seq_swap"))
        # mutate one element (recurse)
        if inner is not None:
            i = rng.randrange(n)
            elem_muts = _mutate_value(v[i], inner, rng, primary_len)
            if elem_muts:
                m = list(v)
                m[i] = elem_muts[0].value
                out.append(Mutant(m, "seq_elem"))

    # insert a value at a random index
    if inner is not None:
        ins = _default_value(inner)
        idx = rng.randint(0, n)
        m = v[:idx] + [ins] + v[idx:]
        out.append(Mutant(m, "seq_insert"))
    # empty
    if n > 0:
        out.append(Mutant([], "seq_empty"))
    # extend by one
    if inner is not None:
        out.append(Mutant(v + [_default_value(inner)], "seq_extend"))

    return [m for m in out if _structurally_ne(m.value, v)]


def _mutate_seq_char(v: str, rng: random.Random) -> list[Mutant]:
    out: list[Mutant] = []
    n = len(v)
    if n > 0:
        i = rng.randrange(n)
        out.append(Mutant(v[:i] + v[i + 1:], "str_drop"))
        out.append(Mutant(v[0] + v, "str_dup"))
        if v[::-1] != v:
            out.append(Mutant(v[::-1], "str_reverse"))
        # replace a char
        i = rng.randrange(n)
        rc = chr((ord(v[i]) + 1))
        out.append(Mutant(v[:i] + rc + v[i + 1:], "str_replace"))
    out.append(Mutant("" if n > 0 else "x", "str_empty"))
    return [m for m in out if _structurally_ne(m.value, v)]


def _mutate_option(v, st: SpecType, rng: random.Random, primary_len: int) -> list[Mutant]:
    inner = st.inner
    out: list[Mutant] = []
    if v is None:
        if inner is not None:
            out.append(Mutant(_default_value(inner), "opt_some"))
    else:
        out.append(Mutant(None, "opt_none"))
        if inner is not None:
            for m in _mutate_value(v, inner, rng, primary_len)[:2]:
                out.append(Mutant(m.value, "opt_inner"))
    return out


def _default_value(st: SpecType):
    if st.kind == "int":
        return 0
    if st.kind == "bool":
        return False
    if st.kind == "char":
        return "a"
    if st.kind == "seq":
        if st.inner and st.inner.kind == "char":
            return ""
        return []
    if st.kind == "option":
        return None
    if st.kind == "tuple":
        return [_default_value(e) for e in (st.elems or [])]
    return 0


def _mutate_value(v, st: SpecType, rng: random.Random, primary_len: int) -> list[Mutant]:
    if st.kind == "int" and isinstance(v, int) and not isinstance(v, bool):
        return _mutate_int(v, st, rng, primary_len)
    if st.kind == "bool" and isinstance(v, bool):
        return _mutate_bool(v)
    if st.kind == "char" and isinstance(v, str):
        return _mutate_char(v)
    if st.kind == "seq":
        if st.inner and st.inner.kind == "char" and isinstance(v, str):
            return _mutate_seq_char(v, rng)
        if isinstance(v, list):
            return _mutate_seq(v, st, rng, primary_len)
    if st.kind == "option":
        return _mutate_option(v, st, rng, primary_len)
    if st.kind == "tuple" and isinstance(v, list) and st.elems:
        out = []
        for i, est in enumerate(st.elems):
            for m in _mutate_value(v[i], est, rng, primary_len)[:2]:
                nv = list(v)
                nv[i] = m.value
                out.append(Mutant(nv, f"tuple_{i}"))
        return out
    return []


def mutate_output(value, st: SpecType, rng: random.Random, k: int, primary_len: int = 0) -> list[Mutant]:
    """Return up to k output mutants, stratified so distinct families appear first.

    Deterministic given rng. Guarantees each returned mutant is structurally
    different from `value`.
    """
    muts = _mutate_value(copy.deepcopy(value), st, rng, primary_len)
    # De-dup by (op, repr) then stratify: one per family first, then fill.
    seen: set = set()
    by_family: dict[str, list[Mutant]] = {}
    for m in muts:
        key = (m.op, repr(m.value))
        if key in seen:
            continue
        seen.add(key)
        by_family.setdefault(m.op, []).append(m)

    ordered: list[Mutant] = []
    # round-robin across families for diversity
    families = list(by_family)
    rng.shuffle(families)
    idx = 0
    while len(ordered) < k and any(by_family.values()):
        fam = families[idx % len(families)]
        if by_family[fam]:
            ordered.append(by_family[fam].pop(0))
        idx += 1
        if idx > k * len(families) + len(families):
            break
    return ordered[:k]

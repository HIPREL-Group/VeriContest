"""Type-aware mutation of existing inputs (EvalPlus-style). Candidate inputs
only — outputs come from the reference driver, and every candidate still
passes the schema and precondition gates."""
from __future__ import annotations

import copy
import random

from spec_testing.common.specmodel import SpecModel
from spec_testing.common.values import spec_type, SpecType


def _mutate_typed(v, st: SpecType, rng: random.Random):
    """One mutated value for the given spec type (recursive)."""
    if st.kind == "int" and isinstance(v, int) and not isinstance(v, bool):
        return rng.choice([v + 1, v - 1, 0, -v, v * 2])
    if st.kind == "bool":
        return not v
    if st.kind == "char" and isinstance(v, str) and v:
        return chr(ord(v[0]) + rng.choice([1, -1]))
    if st.kind == "seq":
        inner = st.inner
        if inner and inner.kind == "char" and isinstance(v, str):
            if not v:
                return "a"
            op = rng.randrange(3)
            i = rng.randrange(len(v))
            if op == 0:
                return v[:i] + v[i + 1:]
            if op == 1:
                return v[:i] + v[i] + v[i:]
            return v[:i] + chr(ord(v[i]) + 1) + v[i + 1:]
        if isinstance(v, list):
            if not v:
                return [_default(inner)] if inner else []
            op = rng.randrange(4)
            i = rng.randrange(len(v))
            if op == 0:
                return v[:i] + v[i + 1:]                     # drop
            if op == 1:
                return v[:i] + [v[i]] + v[i:]                # dup
            if op == 2:
                m = copy.deepcopy(v)
                if inner:
                    m[i] = _mutate_typed(m[i], inner, rng)
                return m
            return v + [_default(inner)] if inner else v     # extend
    if st.kind == "option":
        if v is None and st.inner:
            return _default(st.inner)
        return None
    if st.kind == "tuple" and isinstance(v, list) and st.elems:
        m = copy.deepcopy(v)
        i = rng.randrange(len(m))
        m[i] = _mutate_typed(m[i], st.elems[i], rng)
        return m
    return v


def _default(st: SpecType | None):
    if st is None:
        return 0
    if st.kind == "int":
        return 0
    if st.kind == "bool":
        return False
    if st.kind == "char":
        return "a"
    if st.kind == "seq":
        return "" if (st.inner and st.inner.kind == "char") else []
    if st.kind == "option":
        return None
    if st.kind == "tuple":
        return [_default(e) for e in (st.elems or [])]
    return 0


def mutate_inputs(seed_inputs: list[dict], model: SpecModel, rng: random.Random, k: int) -> list[dict]:
    """Produce up to k mutated input dicts from seed inputs (LC/extended only)."""
    if not seed_inputs:
        return []
    out: list[dict] = []
    types = {p.name: spec_type(p.rust_type) for p in model.params}
    attempts = 0
    while len(out) < k and attempts < k * 8:
        attempts += 1
        base = copy.deepcopy(rng.choice(seed_inputs))
        # mutate one randomly-chosen param
        pname = rng.choice([p.name for p in model.params])
        if pname in base and pname in types:
            base[pname] = _mutate_typed(base[pname], types[pname], rng)
            out.append(base)
    return out

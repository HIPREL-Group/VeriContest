"""Codeforces stdin/stdout -> typed spec-param alignment.

CF cases are raw strings; the verified fn takes typed params. A heuristic
tokenizer covers the dominant CF input shapes and reports failure for anything
it can't align cleanly (unalignable CF cases are skipped, never guessed).

Supported shapes:
  - all-scalar params: N tokens -> N scalar params in order.
  - single Vec<T> param, optionally preceded by scalar params, with an
    optional leading length token (the classic `n \\n a_1..a_n`).
"""
from __future__ import annotations

import re
from dataclasses import dataclass

from spec_testing.common.specmodel import SpecModel
from spec_testing.common.testcases import Case
from spec_testing.common.values import spec_type


@dataclass
class CFAlignment:
    ok: bool
    values: dict          # param_name -> json value
    reason: str = ""


def _tokens(stdin: str) -> list[str]:
    return stdin.split()


_FALSE_TOKENS = ("0", "false", "False", "FALSE", "no", "No", "NO")


def _scalar(tok: str, kind: str):
    if kind == "bool":
        return tok not in _FALSE_TOKENS
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)
    if re.fullmatch(r"-?\d+\.\d+", tok):
        return float(tok)
    return tok


def _align_single_vec(params, vec_p, sts, toks) -> CFAlignment | None:
    """Token-based single-vec alignment; None => caller falls back to Case C."""
    inner_kind = sts[vec_p.name].inner.kind if sts[vec_p.name].inner else "int"
    vals = {}
    idx = 0
    trailing: list = []
    seen_vec = False
    for p in params:
        if p is vec_p:
            seen_vec = True
            continue
        if seen_vec:
            trailing.append(p)
            continue
        if idx >= len(toks):
            return None
        vals[p.name] = _scalar(toks[idx], sts[p.name].kind)
        idx += 1
    if idx >= len(toks):
        return None
    remaining = toks[idx:]
    try:
        n = int(remaining[0])
    except ValueError:
        n = None
    had_len_prefix = n is not None and n == len(remaining) - 1
    body = remaining[1:] if had_len_prefix else remaining
    vals[vec_p.name] = [_scalar(t, inner_kind) for t in body]
    # a scalar param after the vec (e.g. `(heights, n)`) can only be the
    # length — and only when an explicit length prefix confirmed it
    if trailing:
        if len(trailing) == 1 and had_len_prefix and sts[trailing[0].name].kind == "int":
            vals[trailing[0].name] = n
        else:
            return None
    return CFAlignment(True, vals)


def align_cf_input(model: SpecModel, stdin: str) -> CFAlignment:
    toks = _tokens(stdin)
    params = model.params
    sts = {p.name: spec_type(p.rust_type) for p in params}
    vec_params = [p for p in params if sts[p.name].kind == "seq"]
    scalar_params = [p for p in params if sts[p.name].kind in ("int", "bool", "char")]
    if len(vec_params) + len(scalar_params) != len(params):
        return CFAlignment(False, {}, "unsupported param kind")

    # Case A: all scalars. Strict token count — a `t`-testcases blob must not
    # silently misalign onto a single-case signature.
    if not vec_params:
        if len(toks) != len(scalar_params):
            return CFAlignment(False, {}, "token count != scalar params")
        vals = {}
        for i, p in enumerate(scalar_params):
            vals[p.name] = _scalar(toks[i], sts[p.name].kind)
        return CFAlignment(True, vals)

    # Case B: exactly one Vec (classic `scalars.. [n] a_1..a_n`). On failure
    # fall through to the line-structured Case C.
    if len(vec_params) == 1:
        b = _align_single_vec(params, vec_params[0], sts, toks)
        if b is not None:
            return b

    # Case C: line-structured — one line per vec (in signature order), optional
    # first line holding scalars and/or the vec lengths (`n k \n a_1..a_n`).
    # Residual misalignments are caught downstream: every seed must reproduce
    # its stated output through the reference driver before it is stored.
    lines = [ln for ln in stdin.splitlines() if ln.strip()]
    n_vec = len(vec_params)

    # Case D: column-structured — header `n scalars..`, then n rows of exactly
    # one token per vec param; column j feeds vec param j (signature order).
    # Only when the shape cannot also read as one-line-per-vec (rows != vecs).
    if len(lines) >= 2 and n_vec >= 2:
        hdr = lines[0].split()
        body = [ln.split() for ln in lines[1:]]
        try:
            n0 = int(hdr[0])
        except ValueError:
            n0 = None
        if n0 == len(body) and len(body) != n_vec and \
                all(len(row) == n_vec for row in body):
            rest = hdr[1:]
            if len(rest) == len(scalar_params):
                vals = {}
                for h, p in zip(rest, scalar_params):
                    vals[p.name] = _scalar(h, sts[p.name].kind)
                for j, p in enumerate(vec_params):
                    inner_kind = sts[p.name].inner.kind if sts[p.name].inner else "int"
                    vals[p.name] = [_scalar(row[j], inner_kind) for row in body]
                return CFAlignment(True, vals)

    header: list[str] | None = None
    if len(lines) == n_vec + 1:
        header = lines[0].split()
    elif len(lines) != n_vec or scalar_params:
        return CFAlignment(False, {}, f"unsupported CF shape: {n_vec} vecs, {len(lines)} lines")
    body_lines = lines[-n_vec:]
    vals = {}
    vec_toks = [ln.split() for ln in body_lines]
    if header is not None:
        # Consume header left-to-right: a token equal to the next expected vec
        # length is a length marker; anything else fills the next scalar param.
        expected_lens = [len(t) for t in vec_toks]
        scalars_left = list(scalar_params)
        consumed_lens = 0
        for h in header:
            if expected_lens and h.isdigit() and int(h) == expected_lens[0]:
                expected_lens.pop(0)
                consumed_lens += 1
            elif scalars_left:
                p = scalars_left.pop(0)
                vals[p.name] = _scalar(h, sts[p.name].kind)
            else:
                return CFAlignment(False, {}, "unconsumed header token")
        # `(heights, n)` style: a single leftover int scalar takes the length
        if len(scalars_left) == 1 and consumed_lens == 1 and \
                sts[scalars_left[0].name].kind == "int":
            vals[scalars_left[0].name] = len(vec_toks[0])
            scalars_left = []
        if scalars_left:
            return CFAlignment(False, {}, "header too short for scalars")
    for p, tks in zip(vec_params, vec_toks):
        inner_kind = sts[p.name].inner.kind if sts[p.name].inner else "int"
        vals[p.name] = [_scalar(t, inner_kind) for t in tks]
    return CFAlignment(True, vals)


def _parse_cf_output(raw: str, ret_type: str):
    """Parse a CF stdout string into a value of the return type.

    Scalars, tuples of scalars, and a trailing Vec component are supported.
    Strict: every stdout token must be consumed (a multi-testcase blob must
    not misparse as one answer)."""
    st = spec_type(ret_type)
    toks = raw.split()
    if not toks:
        return None

    def _one(tok: str, k: SpecType):
        if k.kind == "bool":
            return tok not in _FALSE_TOKENS
        if k.kind == "int":
            try:
                return int(tok)
            except ValueError:
                return None
        return None

    if st.kind in ("int", "bool"):
        if len(toks) != 1:
            return None
        return _one(toks[0], st)

    if st.kind == "tuple" and st.elems:
        # scalar components only, exact token count — sequence components are
        # ambiguous in CF output format (see below)
        if any(elem.kind not in ("int", "bool") for elem in st.elems):
            return None
        if len(toks) != len(st.elems):
            return None
        out = []
        for tok, elem in zip(toks, st.elems):
            v = _one(tok, elem)
            if v is None:
                return None
            out.append(v)
        return out

    # Sequence-valued outputs are NOT parsed: CF stdout for a list answer is
    # conventionally count-prefixed ("2\n1 4" = the list [1, 4]), but nothing
    # marks the convention per problem, so any reading is a guess. A guessed
    # (input, output) pair could later be *provably rejected* by a sound spec
    # — a false unsoundness finding. Such cases stay execution-only.
    return None


def normalize_cf_case(model: SpecModel, case: Case) -> Case | None:
    """Convert a raw-string CF case into a typed (input dict, output value)
    case, or None when alignment fails."""
    if not isinstance(case.input, str):
        return case
    a = align_cf_input(model, case.input)
    if not a.ok:
        return None
    out = case.output
    if isinstance(out, str):
        out = _parse_cf_output(out, model.ret_type)
        if out is None:
            return None
    return Case(input=a.values, output=out, source=case.source, meta=case.meta)

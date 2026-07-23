"""Exec-mode case harness.

Instead of rewriting ensures/requires to a seq-level `__vc_post` (which breaks
whenever the problem's own helper spec fns use exec container types — the
Seq<Seq<T>> vs Seq<Vec<T>> class, ), build the concrete case
values as *real exec values* (`Vec::push` chains, scalars) and assert the
ORIGINAL clause text verbatim inside a `proof { }` block. Verus resolves
`v[i]` / `v@` / `v.len()` on exec locals natively, so no type mapping and no
`@`-sigil rewriting is needed.

The only rewrites that remain are semantically unavoidable:
  - `&mut p`: `old(p)` -> `__old_p` (pre-state local); bare `p` stays and is
    bound to the post-state local (ensures) or the pre-state local (requires).
  - `Self::` -> `Solution::` (helpers are wrapped in `impl Solution`).

Emits probe fn names `__pre_neg_i` / `__rej_neg_i` / `__acc_neg_i` consumed
via Verus func-details.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

from . import harness
from .specmodel import SpecModel
from .testcases import Case
from .values import SpecType, ValueError_, render_value, spec_type


@dataclass
class RenderedHarness:
    file_text: str
    fn_names: dict[str, tuple[int, str]]
    gen_errors: list[tuple[int, str]] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Exec value construction
# ---------------------------------------------------------------------------

def _exec_type(rust_type: str) -> str:
    """The local's exec type: refs stripped (owned values behave identically
    in spec contexts), everything else verbatim."""
    t = rust_type.strip()
    t = re.sub(r"^&\s*mut\s+", "", t)
    t = re.sub(r"^&\s*", "", t)
    return t


def _scalar_literal(value, st: SpecType) -> str:
    # render_value already emits exec-compatible literals for scalars
    # (3i32 / true / 'a') and raises ValueError_ on range violations.
    return render_value(value, st)


def build_value_stmts(name: str, value, rust_type: str, hint_cap: int,
                      _depth: int = 0) -> tuple[list[str], list[str]]:
    """Return (stmts, hint_asserts) that bind exec local `name` to `value`.

    Supports scalars, String/&str, Option, Vec<T> and Vec<Vec<T>>. Raises
    ValueError_ for unrepresentable shapes (caller maps to GEN_ERROR).
    """
    t = _exec_type(rust_type)
    st = spec_type(t)

    if st.kind in ("int", "bool", "char"):
        return [f"let {name}: {t} = {_scalar_literal(value, st)};"], []

    if t in ("String", "str"):
        if not isinstance(value, str):
            raise ValueError_(f"expected string for {name}: {t}, got {value!r}")
        lit = value.replace("\\", "\\\\").replace('"', '\\"')
        stmts = [f'let {name}: &str = "{lit}";']
        return stmts, [f'reveal_strlit("{lit}");',
                       f"assert({name}@.len() == {len(value)});"]

    m = re.match(r"^Option\s*<(.+)>$", t)
    if m:
        inner_t = m.group(1).strip()
        ist = spec_type(inner_t)
        if value is None:
            return [f"let {name}: Option<{inner_t}> = None;"], []
        if ist.kind in ("int", "bool", "char"):
            return [f"let {name}: Option<{inner_t}> = Some({_scalar_literal(value, ist)});"], []
        raise ValueError_(f"unsupported Option inner type {inner_t!r}")

    m = re.match(r"^Vec\s*<(.+)>$", t)
    if m:
        inner_t = m.group(1).strip()
        ist = spec_type(inner_t)
        # Vec<char> encoded as a JSON string
        if ist.kind == "char" and isinstance(value, str):
            value = list(value)
        if not isinstance(value, list):
            raise ValueError_(f"expected list for {name}: {t}, got {value!r}")

        stmts: list[str] = []
        hints: list[str] = []
        if ist.kind in ("int", "bool", "char"):
            if not value:
                stmts.append(f"let {name}: Vec<{inner_t}> = Vec::new();")
            else:
                stmts.append(f"let mut {name}: Vec<{inner_t}> = Vec::new();")
                for v in value:
                    stmts.append(f"{name}.push({_scalar_literal(v, ist)});")
            hints.append(f"assert({name}@.len() == {len(value)});")
            hints.append(f"assert({name}.len() == {len(value)});")
            for k, v in enumerate(value[:hint_cap]):
                hints.append(f"assert({name}@[{k}] == {_scalar_literal(v, ist)});")
                # spec-index form: seeds `#[trigger] name[i]`-style quantifier
                # triggers and unifies the two term families
                hints.append(f"assert({name}[{k}] == {name}@[{k}]);")
            return stmts, hints

        if re.match(r"^(?:Vec|String)\b", inner_t) or ist.kind == "seq":
            # nested: build inner locals first, then push (move) them
            if not value:
                stmts.append(f"let {name}: Vec<{inner_t}> = Vec::new();")
            else:
                inner_names = []
                for k, elem in enumerate(value):
                    iname = f"__{name}_{k}"
                    istmts, ihints = build_value_stmts(iname, elem, inner_t, hint_cap, _depth + 1)
                    stmts += istmts
                    hints += ihints
                    inner_names.append(iname)
                stmts.append(f"let mut {name}: Vec<{inner_t}> = Vec::new();")
                for iname in inner_names:
                    stmts.append(f"{name}.push({iname});")
            hints.append(f"assert({name}@.len() == {len(value)});")
            hints.append(f"assert({name}.len() == {len(value)});")
            # re-anchor inner facts on the outer view (inner locals are moved)
            for k, elem in enumerate(value[:hint_cap]):
                hints.append(f"assert({name}[{k}] == {name}@[{k}]);")
                if isinstance(elem, list):
                    hints.append(f"assert({name}@[{k}]@.len() == {len(elem)});")
                    iist = spec_type(_exec_type(inner_t))
                    if iist.inner is not None and iist.inner.kind in ("int", "bool", "char"):
                        for kk, vv in enumerate(elem[:hint_cap]):
                            hints.append(f"assert({name}@[{k}]@[{kk}] == {_scalar_literal(vv, iist.inner)});")
                            hints.append(f"assert({name}@[{k}][{kk}] == {name}@[{k}]@[{kk}]);")
            return stmts, hints

        raise ValueError_(f"unsupported Vec inner type {inner_t!r}")

    raise ValueError_(f"unsupported exec type {t!r}")


# ---------------------------------------------------------------------------
# Clause rewriting (minimal: &mut era naming + Self::)
# ---------------------------------------------------------------------------

def rewrite_clause_exec(clause: str, model: SpecModel, context: str) -> str:
    """context: 'requires' (bare &mut name = pre-state) or 'ensures'
    (bare &mut name = post-state, dataset 'old' style)."""
    text = clause
    for p in model.params:
        if not p.is_mut_ref:
            continue
        text = re.sub(rf"\bold\s*\(\s*{re.escape(p.name)}\s*\)", f"__old_{p.name}", text)
        text = re.sub(rf"\bfinal\s*\(\s*{re.escape(p.name)}\s*\)", p.name, text)
        if context == "requires":
            # requires are evaluated at entry: bare name is the pre-state
            text = re.sub(rf"\b{re.escape(p.name)}\b", f"__old_{p.name}", text)
    return harness.rewrite_self_calls(text.strip())


def _post_expr(model: SpecModel) -> str:
    clauses = []
    if model.returns_expr is not None:
        expr = rewrite_clause_exec(model.returns_expr, model, "ensures")
        clauses.append(f"{model.ret_name} == ({expr})")
    for c in model.ensures:
        clauses.append(rewrite_clause_exec(c, model, "ensures"))
    if not clauses:
        return "true"
    return "\n        && ".join(f"({c})" for c in clauses)


def _pre_expr(model: SpecModel) -> str:
    if not model.requires:
        return "true"
    return "\n        && ".join(f"({rewrite_clause_exec(c, model, 'requires')})" for c in model.requires)


# ---------------------------------------------------------------------------
# Fuel / reveal hints (shared logic with the spec path lives in harness.py)
# ---------------------------------------------------------------------------

def _reveal_hints(model: SpecModel, concrete_values: list) -> list[str]:
    fuel = harness.compute_fuel(concrete_values)
    return [f"reveal_with_fuel({path}, {fuel});"
            for path in harness.recursive_helper_paths(model)] + \
        harness.strlit_hints(model)


def _value_env(model: SpecModel, case: Case) -> dict:
    env = dict(case.input) if isinstance(case.input, dict) else {}
    out = case.output
    ret = out.get("ret") if (model.has_mut_ref and isinstance(out, dict)) else out
    env.setdefault(model.ret_name, ret)
    return env


# ---------------------------------------------------------------------------
# Case rendering
# ---------------------------------------------------------------------------

def _case_bindings(model: SpecModel, case: Case, role: str,
                   hint_cap: int) -> tuple[list[str], list[str], list]:
    """Build (stmts, hints, concrete_values) for one case.

    role 'pre': bind param pre-states only (requires probe).
    role 'post': bind pre+post &mut states and the ret value (ensures probes).
    """
    inp = case.input if isinstance(case.input, dict) else {}
    stmts: list[str] = []
    hints: list[str] = []
    vals: list = []

    for p in model.params:
        pre_val = inp.get(p.name)
        if pre_val is None and spec_type(_exec_type(p.rust_type)).kind != "option":
            raise ValueError_(f"missing input value for {p.name}")
        vals.append(pre_val)
        if p.is_mut_ref:
            s, h = build_value_stmts(f"__old_{p.name}", pre_val, p.rust_type, hint_cap)
            stmts += s
            hints += h
            if role == "post":
                post = case.output
                post_val = post.get(f"{p.name}_after") if isinstance(post, dict) else None
                if post_val is None:
                    raise ValueError_(f"missing {p.name}_after in output")
                vals.append(post_val)
                s, h = build_value_stmts(p.name, post_val, p.rust_type, hint_cap)
                stmts += s
                hints += h
        else:
            s, h = build_value_stmts(p.name, pre_val, p.rust_type, hint_cap)
            stmts += s
            hints += h

    if role == "post":
        out = case.output
        ret_val = out.get("ret") if (model.has_mut_ref and isinstance(out, dict)) else out
        vals.append(ret_val)
        if any(p.name == model.ret_name for p in model.params):
            raise ValueError_(f"ret name {model.ret_name!r} collides with a param")
        s, h = build_value_stmts(model.ret_name, ret_val, model.ret_type, hint_cap)
        stmts += s
        hints += h
        hints += harness.strlit_ext_hints(model, f"{model.ret_name}@")

    return stmts, hints, vals


def _probe_fn(fn_name: str, stmts: list[str], proof_lines: list[str], assertion: str) -> str:
    body = "\n    ".join(stmts)
    proof = "\n        ".join(proof_lines + [assertion])
    return f"fn {fn_name}() {{\n    {body}\n    proof {{\n        {proof}\n    }}\n}}"


def render_exec_harness(model: SpecModel, neg_cases: list[Case],
                        hint_cap: int = 64) -> RenderedHarness:
    helpers_text, _ = harness.render_helpers(model)
    pre_expr = _pre_expr(model)
    post_expr = _post_expr(model)

    fn_names: dict[str, tuple[int, str]] = {}
    gen_errors: list[tuple[int, str]] = []
    blocks: list[str] = []

    from spec_testing.common.config import get as _get
    sat_budget = int(_get("harness", "exists_sat_budget", 128))
    post_clauses = [rewrite_clause_exec(c, model, "ensures") for c in model.ensures]

    def _render_case(case: Case, idx: int):
        try:
            stmts, hints, vals = _case_bindings(model, case, "pre", hint_cap)
            reveal = _reveal_hints(model, vals)
            blocks.append(_probe_fn(f"__pre_neg_{idx}", stmts, reveal + hints,
                                    f"assert({pre_expr});"))
            fn_names[f"__pre_neg_{idx}"] = (idx, "pre")
            stmts, hints, vals = _case_bindings(model, case, "post", hint_cap)
            reveal = _reveal_hints(model, vals) + \
                harness.bitop_hints(model, _value_env(model, case))
            hints = hints + harness.exists_saturation(post_clauses, vals, sat_budget)
            blocks.append(_probe_fn(f"__rej_neg_{idx}", stmts, reveal + hints,
                                    f"assert(!({post_expr}));"))
            fn_names[f"__rej_neg_{idx}"] = (idx, "rej")
            blocks.append(_probe_fn(f"__acc_neg_{idx}", stmts, reveal + hints,
                                    f"assert({post_expr});"))
            fn_names[f"__acc_neg_{idx}"] = (idx, "acc")
        except ValueError_ as exc:
            gen_errors.append((idx, f"value:{exc}"))
        except Exception as exc:  # noqa: BLE001
            gen_errors.append((idx, f"render:{exc}"))

    for i, c in enumerate(neg_cases):
        _render_case(c, i)

    file_text = "\n\n".join(x for x in [
        "use vstd::prelude::*;",
        harness.render_uses(model),
        "fn main() {}",
        "verus! {",
        "\n".join(model.consts),
        helpers_text,
        "\n\n".join(blocks),
        "}",
    ] if x.strip() or x == "}")
    return RenderedHarness(file_text=file_text, fn_names=fn_names, gen_errors=gen_errors)


# ---------------------------------------------------------------------------
# Dispatcher: pick spec-level (fast, legacy) or exec-mode by shape
# ---------------------------------------------------------------------------

def render_harness_auto(model: SpecModel, neg_cases: list[Case],
                        hint_cap: int = 64, mode: str | None = None):
    """mode: None => auto (exec iff spec_shape.needs_exec_harness); 'spec'|'exec' force."""
    from . import spec_shape
    if mode is None:
        mode = "exec" if spec_shape.needs_exec_harness(model) else "spec"
    if mode == "exec":
        return render_exec_harness(model, neg_cases, hint_cap)
    from . import spec_harness  # local import: avoid cycle
    return spec_harness.render_harness(model, neg_cases, hint_cap)

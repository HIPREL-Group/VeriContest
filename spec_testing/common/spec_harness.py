"""Spec-level concrete-case harness: rewrites the ground-truth clauses into
Seq/int-typed `__vc_pre`/`__vc_post` spec fns and renders, per case, a `__pre`
gate, a `__rej` probe (assert !post) and an `__acc` probe (assert post).
Per-case verdicts come from Verus func-details in a single run.

This is the fast path for flat-typed problems; nested-container problems use
exec_harness (see exec_harness.render_harness_auto for the dispatch).
"""
from __future__ import annotations

from dataclasses import dataclass, field

from spec_testing.common import harness
from spec_testing.common.specmodel import SpecModel
from spec_testing.common.testcases import Case
from spec_testing.common.values import ValueError_


@dataclass
class CaseHarness:
    pre_fn: str
    rej_fn: str | None = None
    acc_fn: str | None = None
    error: str = ""           # GEN_ERROR reason if rendering failed


@dataclass
class RenderedHarness:
    file_text: str
    fn_names: dict[str, tuple[int, str]]   # fn_name -> (case_idx, role)
    gen_errors: list[tuple[int, str]] = field(default_factory=list)


def _input_bindings(model: SpecModel, case: Case) -> list[tuple[harness.SpecParam, object]]:
    """Map spec params to concrete input values for `let` bindings.

    For &mut, both __old and __new take input pre-state / output post-state. The
    pre-state comes from case.input; the post-state comes from case.output's
    '<p>_after' component.
    """
    out: list[tuple[harness.SpecParam, object]] = []
    inp = case.input if isinstance(case.input, dict) else {}
    for sp in harness.spec_params(model):
        if sp.role == "old":
            out.append((sp, inp.get(sp.origin)))
        elif sp.role == "new":
            post = case.output
            key = f"{sp.origin}_after"
            val = post.get(key) if isinstance(post, dict) else None
            out.append((sp, val))
        else:
            out.append((sp, inp.get(sp.origin)))
    return out


def _output_value(model: SpecModel, case: Case):
    """The ret value to plug into __vc_post's ret slot."""
    if model.has_mut_ref:
        if isinstance(case.output, dict):
            return case.output.get("ret")
        return case.output
    return case.output


def _render_case(model: SpecModel, case: Case, idx: int, kind: str,
                 hint_cap: int) -> CaseHarness:
    try:
        bindings = _input_bindings(model, case)
        if any(v is None and sp.st.kind != "option" for sp, v in bindings):
            return CaseHarness("", error="missing_binding")
        ret_val = _output_value(model, case)
        rp = harness.ret_spec_param(model)

        all_vals = list(bindings) + [(rp, ret_val)]
        lets = harness.render_lets(all_vals)
        hints = harness.render_hints(all_vals, model, hint_cap)
        hints += harness.strlit_ext_hints(model, rp.name)
        env = dict(case.input) if isinstance(case.input, dict) else {}
        env.setdefault(model.ret_name, ret_val)
        hints = harness.bitop_hints(model, env) + hints
        from spec_testing.common.config import get as _get
        post_clauses = [harness.rewrite_clause(c, model) for c in model.ensures]
        hints += harness.exists_saturation(
            post_clauses, [v for _, v in all_vals],
            int(_get("harness", "exists_sat_budget", 128)))
        arg_names = ", ".join(sp.name for sp, _ in bindings)
        call_args = arg_names + (", " if arg_names else "") + rp.name

        lets_block = "\n    ".join(lets)
        hints_block = "\n    ".join(hints)
        pre_args = ", ".join(sp.name for sp, _ in bindings)

        pre = (f"proof fn __pre_{kind}_{idx}() {{\n    {lets_block}\n"
               f"    assert(__vc_pre({pre_args}));\n}}")
        rej = (f"proof fn __rej_{kind}_{idx}() {{\n    {lets_block}\n    {hints_block}\n"
               f"    assert(!__vc_post({call_args}));\n}}")
        acc = (f"proof fn __acc_{kind}_{idx}() {{\n    {lets_block}\n    {hints_block}\n"
               f"    assert(__vc_post({call_args}));\n}}")
        return CaseHarness(pre, rej, acc)
    except ValueError_ as exc:
        return CaseHarness("", error=f"value_range:{exc}")
    except Exception as exc:  # noqa: BLE001
        return CaseHarness("", error=f"render:{exc}")


def render_harness(model: SpecModel, neg_cases: list[Case],
                   hint_cap: int = 64) -> RenderedHarness:
    helpers_text, _ = harness.render_helpers(model)
    pre_fn = harness.build_pre_fn(model)
    post_fn = harness.build_post_fn(model)

    fn_names: dict[str, tuple[int, str]] = {}
    gen_errors: list[tuple[int, str]] = []
    blocks: list[str] = []

    for i, c in enumerate(neg_cases):
        ch = _render_case(model, c, i, "neg", hint_cap)
        if ch.error:
            gen_errors.append((i, ch.error))
            continue
        blocks.append(ch.pre_fn)
        blocks.append(ch.rej_fn)
        blocks.append(ch.acc_fn)
        fn_names[f"__pre_neg_{i}"] = (i, "pre")
        fn_names[f"__rej_neg_{i}"] = (i, "rej")
        fn_names[f"__acc_neg_{i}"] = (i, "acc")

    file_text = "\n\n".join(x for x in [
        "use vstd::prelude::*;",
        harness.render_uses(model),
        "fn main() {}",
        "verus! {",
        "\n".join(model.consts),
        helpers_text,
        pre_fn,
        post_fn,
        "\n\n".join(blocks),
        "}",
    ] if x.strip() or x == "}")
    return RenderedHarness(file_text=file_text, fn_names=fn_names, gen_errors=gen_errors)

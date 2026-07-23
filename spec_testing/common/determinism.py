"""Spec output-determinism probe: pre(x) && post(x, r1) && post(x, r2) ==> r1 == r2."""
from __future__ import annotations

import tempfile
from pathlib import Path

from spec_testing.common import harness
from spec_testing.common.specmodel import SpecModel
from spec_testing.common.verusrun import run_verus, find_verus_binary


def _post_fn_named(model: SpecModel, name: str, ensures: list[str],
                   shallow: bool = False) -> str:
    """Build a __vc_post variant with a custom name and a specific ensures list."""
    sps = harness.spec_params(model, shallow)
    rp = harness.ret_spec_param(model, shallow)
    decls = ", ".join(f"{sp.name}: {sp.st}" for sp in sps + [rp])
    clauses = [harness.rewrite_clause(c, model) for c in ensures]
    body = "\n".join(f"    &&& ({c})" for c in clauses) if clauses else "    &&& true"
    text = f"pub open spec fn {name}({decls}) -> bool {{\n{body}\n}}"
    return harness.rewrite_self_calls(text)


def check_determinism(model: SpecModel, rlimit: float = 60,
                      timeout_s: int = 240) -> str:
    """Does the spec pin the output uniquely per valid input?

    Returns "unique" (proved) or "unknown" (anything else — Verus can't
    return countermodels, so multi-output can't be distinguished from solver
    failure; consumers must treat unknown conservatively: diff-based
    wrongness is then only a hint, never a confirmed finding).
    """
    if find_verus_binary() is None:
        return "unknown"
    from spec_testing.common import spec_shape
    shallow = spec_shape.needs_exec_harness(model)

    if model.returns_expr is not None:
        # a `returns <expr>` spec is an equality — deterministic by shape
        return "unique"

    helpers_text, _ = harness.render_helpers(model)
    pre_fn = harness.build_pre_fn(model, shallow)
    post_fn = _post_fn_named(model, "__post_orig", model.ensures, shallow)

    sps = harness.spec_params(model, shallow)
    rp = harness.ret_spec_param(model, shallow)
    p_decls = ", ".join(f"{sp.name}: {sp.st}" for sp in sps)
    p_args = ", ".join(sp.name for sp in sps)
    sep = ", " if p_decls else ""
    probe = (f"proof fn __determinism({p_decls}{sep}__r1: {rp.st}, __r2: {rp.st})\n"
             f"    requires __vc_pre({p_args}), "
             f"__post_orig({p_args}{sep}__r1), __post_orig({p_args}{sep}__r2)\n"
             f"    ensures __r1 == __r2\n{{}}")

    file_text = "\n\n".join(x for x in [
        "use vstd::prelude::*;", harness.render_uses(model), "fn main() {}", "verus! {",
        "\n".join(model.consts), helpers_text, pre_fn, post_fn, probe, "}",
    ] if x.strip() or x == "}")
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "det.rs"
        f.write_text(file_text, encoding="utf-8")
        r = run_verus(f, rlimit=rlimit, timeout_s=timeout_s)
    if r.status not in ("tool_error", "compile_error", "vir_error") and \
            r.func_details.get("__determinism"):
        return "unique"
    return "unknown"

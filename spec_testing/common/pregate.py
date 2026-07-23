"""Three-way precondition gate.

For each candidate input, two probes:
    __pre_i   : assert( <requires conjunction> )    -> PROVED if verified
    __npre_i  : assert(!(<requires conjunction>))   -> REFUTED if verified

Verdicts per input: "proved" | "refuted" | "unknown" | "contradictory".
Only *refuted* inputs are provably illegal and may be dropped; *unknown* is a
solver limitation and is never treated as a rejection.

Rendering uses the exec-mode value builders (real Vec locals + ground hint
asserts), so quantified requires get their trigger seeds and nested-container
problems compile. Falls back to the legacy spec-level rendering per problem if
the exec file fails to compile.
"""
from __future__ import annotations

import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from . import harness
from .exec_harness import _case_bindings, _pre_expr, _probe_fn
from .specmodel import SpecModel
from .testcases import Case
from .values import ValueError_
from .verusrun import find_verus_binary, run_verus

PROVED = "proved"
REFUTED = "refuted"
UNKNOWN = "unknown"
CONTRADICTORY = "contradictory"


@dataclass
class PreGateReport:
    available: bool
    per_input: dict[int, str] = field(default_factory=dict)   # index -> verdict
    status: str = "ran"
    detail: str = ""
    mode: str = "exec"


def _render_exec(model: SpecModel, inputs: list[dict], hint_cap: int) -> tuple[str, dict[int, str]]:
    from .config import get as _get
    from .exec_harness import rewrite_clause_exec
    pre_expr = _pre_expr(model)
    helpers_text, _ = harness.render_helpers(model)
    pre_clauses = [rewrite_clause_exec(c, model, "requires") for c in model.requires]
    sat_budget = int(_get("harness", "exists_sat_budget", 128))
    blocks: list[str] = []
    errors: dict[int, str] = {}
    for i, inp in enumerate(inputs):
        try:
            stmts, hints, vals = _case_bindings(model, Case(input=inp, output=None), "pre", hint_cap)
            fuel_hints = _fuel_hints(model, vals)
            # ground instantiations for quantified requires (e.g. bounds on a
            # recursive helper over all index pairs)
            hints = hints + harness.exists_saturation(pre_clauses, vals, sat_budget)
            blocks.append(_probe_fn(f"__pre_{i}", stmts, fuel_hints + hints, f"assert({pre_expr});"))
            blocks.append(_probe_fn(f"__npre_{i}", stmts, fuel_hints + hints, f"assert(!({pre_expr}));"))
        except (ValueError_, Exception) as exc:  # noqa: BLE001
            errors[i] = f"{type(exc).__name__}: {exc}"
    text = "\n\n".join(x for x in [
        "use vstd::prelude::*;", harness.render_uses(model), "fn main() {}", "verus! {",
        "\n".join(model.consts), helpers_text, "\n\n".join(blocks), "}",
    ] if x.strip() or x == "}")
    return text, errors


def _fuel_hints(model: SpecModel, vals: list) -> list[str]:
    fuel = harness.compute_fuel(vals)
    return [f"reveal_with_fuel({path}, {fuel});" for path in harness.recursive_helper_paths(model)]


def _render_spec(model: SpecModel, inputs: list[dict], hint_cap: int) -> tuple[str, dict[int, str]]:
    """Legacy spec-level fallback (__vc_pre with lets + hints)."""
    pre_fn = harness.build_pre_fn(model)
    helpers_text, _ = harness.render_helpers(model)
    sps = harness.spec_params(model)
    blocks: list[str] = []
    errors: dict[int, str] = {}
    for i, inp in enumerate(inputs):
        try:
            pairs = []
            for sp in sps:
                val = inp.get(sp.origin)
                if val is None and sp.st.kind != "option":
                    raise ValueError_(f"missing input {sp.origin}")
                pairs.append((sp, val))
            lets = harness.render_lets(pairs)
            hints = harness.render_hints(pairs, model, hint_cap)
            args = ", ".join(sp.name for sp, _ in pairs)
            body = "\n    ".join(lets + hints)
            blocks.append(f"proof fn __pre_{i}() {{\n    {body}\n    assert(__vc_pre({args}));\n}}")
            blocks.append(f"proof fn __npre_{i}() {{\n    {body}\n    assert(!__vc_pre({args}));\n}}")
        except (ValueError_, Exception) as exc:  # noqa: BLE001
            errors[i] = f"{type(exc).__name__}: {exc}"
    text = "\n\n".join(x for x in [
        "use vstd::prelude::*;", harness.render_uses(model), "fn main() {}", "verus! {",
        "\n".join(model.consts), helpers_text, pre_fn, "\n\n".join(blocks), "}",
    ] if x.strip() or x == "}")
    return text, errors


def input_size(input_obj) -> int:
    """Total container payload of an input (elements across all params)."""
    total = 0
    vals = input_obj.values() if isinstance(input_obj, dict) else [input_obj]
    for v in vals:
        if isinstance(v, (list, str)):
            total += len(v)
            for e in v if isinstance(v, list) else ():
                if isinstance(e, (list, str)):
                    total += len(e)
    return total


def _check_batch(model: SpecModel, inputs: list[dict], rlimit: float,
                 timeout_s: int, hint_cap: int) -> tuple[dict[int, str], str, str]:
    for mode, renderer in (("exec", _render_exec), ("spec", _render_spec)):
        text, render_errors = renderer(model, inputs, hint_cap)
        with tempfile.TemporaryDirectory() as td:
            f = Path(td) / f"pregate_{model.problem_id}.rs"
            f.write_text(text, encoding="utf-8")
            r = run_verus(f, rlimit=rlimit, timeout_s=timeout_s)
        if r.status in ("compile_error", "vir_error", "tool_error", "timeout"):
            continue  # try the other rendering mode
        per: dict[int, str] = {}
        for i in range(len(inputs)):
            if i in render_errors:
                per[i] = UNKNOWN
                continue
            pos = r.func_details.get(f"__pre_{i}")
            neg = r.func_details.get(f"__npre_{i}")
            if pos and neg:
                per[i] = CONTRADICTORY
            elif pos:
                per[i] = PROVED
            elif neg:
                per[i] = REFUTED
            else:
                per[i] = UNKNOWN
        return per, mode, r.status
    return {i: UNKNOWN for i in range(len(inputs))}, "none", "all_modes_failed"


def check_inputs(model: SpecModel, inputs: list[dict], *, rlimit: float = 30,
                 timeout_s: int = 240, hint_cap: int = 64,
                 batch_size: int = 8, size_cap: int = 256) -> PreGateReport:
    """Batched three-way gate. Oversize inputs (symbolically intractable —
    e.g. a 10k-element array is thousands of pushes/lets) get UNKNOWN without
    being rendered, and a pathological batch can only poison itself."""
    if find_verus_binary() is None:
        return PreGateReport(available=False, status="skip", detail="verus unavailable")
    if not model.requires:
        return PreGateReport(available=True, per_input={i: PROVED for i in range(len(inputs))},
                             detail="no requires")

    per: dict[int, str] = {}
    todo: list[int] = []
    for i, inp in enumerate(inputs):
        if input_size(inp) > size_cap:
            per[i] = UNKNOWN
        else:
            todo.append(i)

    mode_used = "exec"
    details: list[str] = []
    for b in range(0, len(todo), batch_size):
        idxs = todo[b:b + batch_size]
        batch_per, mode, det = _check_batch(model, [inputs[i] for i in idxs],
                                            rlimit, timeout_s, hint_cap)
        mode_used = mode
        details.append(det)
        for local, i in enumerate(idxs):
            per[i] = batch_per.get(local, UNKNOWN)

    return PreGateReport(available=True, per_input=per, status="ran",
                         detail=",".join(sorted(set(details)))[:120], mode=mode_used)

"""Negative test-case assembly from positives: typed output mutation and
cross-case outputs. Each row is tagged with its provenance source."""
from __future__ import annotations

import json

from spec_testing.common import specmodel
from spec_testing.common.values import spec_type
from . import outmut


def _primary_len(input_obj) -> int:
    if isinstance(input_obj, dict):
        for v in input_obj.values():
            if isinstance(v, list):
                return len(v)
    return 0


def _output_components(model: specmodel.SpecModel):
    """Return [(component_key, spec_type)] for the output. Non-mut: [("", ret_st)].
    &mut composite: [("ret", ret_st), ("<p>_after", param_st), ...]."""
    if not model.has_mut_ref:
        return [("", spec_type(model.ret_type))]
    comps = [("ret", spec_type(model.ret_type))]
    for p in model.params:
        if p.is_mut_ref:
            comps.append((f"{p.name}_after", spec_type(p.rust_type)))
    return comps


def _get_component(output, key: str):
    if key == "":
        return output
    if isinstance(output, dict):
        return output.get(key)
    # Bare output for a &mut problem = the ret value only (post-state not
    # captured, e.g. driver couldn't run). Allow mutating the ret component.
    if key == "ret":
        return output
    return None


def _set_component(output, key: str, val):
    if key == "":
        return val
    if isinstance(output, dict):
        new = dict(output)
        new[key] = val
        return new
    # Bare output: only the ret component is representable.
    if key == "ret":
        return val
    return output


def _cf_scalar_mutate(model, positives, rng, k_outmut) -> list[dict]:
    """CF outputs are raw strings; parse a scalar (single-line int/bool) output,
    mutate it as a typed value, and re-serialize to a string for the store."""
    negs: list[dict] = []
    st = spec_type(model.ret_type)
    if st.kind not in ("int", "bool"):
        return negs
    for pos in positives:
        raw = pos["output"]
        toks = str(raw).split()
        if len(toks) != 1:
            continue
        try:
            val = int(toks[0]) if st.kind == "int" else (toks[0] not in ("0", "false"))
        except ValueError:
            continue
        for m in outmut.mutate_output(val, st, rng, k_outmut, _primary_len(pos["input"])):
            new_raw = str(m.value).lower() if st.kind == "bool" else str(m.value)
            if new_raw == str(raw).strip():
                continue
            negs.append({"input": pos["input"], "output": new_raw,
                         "source": "outmut", "meta": {"op": m.op, "component": "ret"}})
    return negs


def gen_negatives(model, positives, rng, k_outmut, k_cross):
    """Assemble outmut + cross negatives from positives. Returns list of dicts."""
    negs: list[dict] = []
    comps = _output_components(model)

    from spec_testing.common import cf_io
    use_cf_typed = (model.kind == "codeforces" and cf_io.is_cf_io_supported(model.problem_id)
                    and positives and not isinstance(positives[0]["output"], str))

    if model.kind == "codeforces" and not use_cf_typed:
        # Unsupported CF outputs are raw strings; use the scalar-parse path.
        negs.extend(_cf_scalar_mutate(model, positives, rng, k_outmut))
    else:
        # Source 1: typed output mutation, per positive case, per component.
        # Sequence-typed components have a far larger mutation space than
        # scalars (per-position ops), so they get a doubled draw budget.
        for pos in positives:
            primary_len = _primary_len(pos["input"])

            for key, st in comps:
                comp_val = _get_component(pos["output"], key)
                if comp_val is None:
                    continue
                k_eff = k_outmut * (2 if st.kind == "seq" else 1)
                for m in outmut.mutate_output(comp_val, st, rng, k_eff, primary_len):
                    new_out = _set_component(pos["output"], key, m.value)
                    if new_out == pos["output"]:
                        continue
                    negs.append({
                        "input": pos["input"], "output": new_out,
                        "source": "outmut", "meta": {"op": m.op, "component": key or "ret"},
                    })

    # Source 2: cross-case outputs (input A with correct output of input B).
    # Deterministic enumeration: pairs whose wrong value is not yet used come
    # first, then remaining pairs fill up to k_cross. (Random draws with
    # replacement wasted most of the budget on collisions.)
    if len(positives) >= 2:
        all_pairs = []
        for i, a in enumerate(positives):
            for j, b in enumerate(positives):
                if i == j or a["output"] == b["output"]:
                    continue
                all_pairs.append((i, j, a, b))
        seen_vals: set[str] = set()
        chosen: list[tuple] = []
        rest: list[tuple] = []
        for i, j, a, b in all_pairs:
            v = json.dumps(b["output"], sort_keys=True, default=str)
            if v not in seen_vals:
                seen_vals.add(v)
                chosen.append((i, j, a, b))
            else:
                rest.append((i, j, a, b))
        for i, j, a, b in (chosen + rest)[:k_cross]:
            negs.append({"input": a["input"], "output": b["output"],
                         "source": "cross", "meta": {"from": b.get("id", j)}})

    return negs

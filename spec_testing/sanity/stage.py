"""Sanity-vacuity-check stage: static checks S1-S7, vacuity probes V1/V1S,
seed-precondition check, and spec-shape classification.

Pure: returns the report dict; persisting it is the caller's choice.
"""
from __future__ import annotations

from pathlib import Path

from spec_testing.common import pregate, specmodel
from spec_testing.common.config import get
from spec_testing.sanity import ast_checks, vacuity


def _seed_pre_check(problem, model) -> tuple[dict, int]:
    """Description examples that provably violate requires mean the requires
    contradicts the problem statement. Returns (report, n_refuted).

    Codeforces inputs are taken from the arg-capture driver (the exact typed
    values the reference main() feeds the fn) rather than a heuristic stdin
    parse, so correct representations (e.g. cf146A's digit split) are never
    mis-parsed into spurious refutations."""
    from spec_testing.testgen.validate import gate_schema

    if problem.is_codeforces:
        import tempfile
        from spec_testing.testgen import driver as driver_mod
        with tempfile.TemporaryDirectory() as td:
            inputs = [pair["input"]
                      for pair in driver_mod.capture_seeds(problem, model, Path(td))
                      if gate_schema(pair["input"], model).ok]
    else:
        from spec_testing.testgen import seeds as seeds_mod
        sr = seeds_mod.extract_seeds(problem, model)
        inputs = [s.input for s in sr.seeds
                  if isinstance(s.input, dict) and gate_schema(s.input, model).ok]

    if not inputs:
        return {"n_seeds": 0, "refuted": 0, "status": "skip:no_seeds"}, 0

    rep = pregate.check_inputs(model, inputs,
                               rlimit=float(get("pregate", "rlimit", 30)),
                               batch_size=int(get("pregate", "batch", 8)),
                               size_cap=int(get("pregate", "size_cap", 256)))
    if not rep.available:
        return {"n_seeds": len(inputs), "refuted": 0, "status": rep.status}, 0
    refuted = sum(1 for v in rep.per_input.values()
                  if v in ("refuted", "contradictory"))
    return {"n_seeds": len(inputs), "refuted": refuted, "status": rep.mode}, refuted


def run(problem) -> dict:
    m = specmodel.load_spec_model(problem)
    if isinstance(m, specmodel.GenError):
        return {"unsupported": m.reason}

    flags: list[dict] = []

    for f in ast_checks.run_static(m):
        flags.append({"check": f.check, "probe": f.check, "severity": f.severity,
                      "message": f.message, "clause": getattr(f, "clause", "")})

    v_flags, v_status = vacuity.run_vacuity(
        problem, m,
        rlimit=float(get("sanity", "vacuity_rlimit", 10)),
        timeout_s=int(get("run", "verus_timeout_s", 300)))
    for f in v_flags:
        flags.append({"probe": f.probe, "severity": f.severity, "message": f.message})

    seed_pre, n_refuted = _seed_pre_check(problem, m)
    if n_refuted:
        flags.append({"probe": "SEED_PRE_REFUTED", "severity": "FLAG_HIGH",
                      "message": f"{n_refuted} description example(s) provably "
                                 f"violate requires -> requires contradicts the "
                                 f"problem statement"})

    return {
        "flags": flags,
        "vacuity_status": v_status,
        "seed_pre": seed_pre,
    }

"""Per-case Verus probe primitives.

Each case renders as up to three proof fns — __pre_neg_i (precondition),
__rej_neg_i (spec provably rejects the pair), __acc_neg_i (spec provably
accepts) — and the raw verdict is read off which probes verify. A failed
probe is never evidence: only positive proofs decide.
"""
from __future__ import annotations

import re
import tempfile
import time
from pathlib import Path

from spec_testing.common.config import get
from spec_testing.common.exec_harness import render_harness_auto
from spec_testing.common.testcases import Case
from spec_testing.common.verusrun import run_verus


def quantifier_free(model) -> bool:
    text = "\n".join(model.ensures) + (model.returns_expr or "")
    return not re.search(r"\b(forall|exists)\b", text)


def _budget_timeout(timeout_s: int, deadline: float | None) -> int | None:
    """Effective Verus wall timeout, clamped to the per-problem deadline.
    None means the deadline has already passed (caller aborts to UNDECIDED)."""
    if deadline is None:
        return timeout_s
    rem = deadline - time.monotonic()
    if rem <= 0:
        return None
    return max(1, min(timeout_s, int(rem)))


def _inject_compute_fn(text: str, fn_name: str) -> str:
    """Append `by (compute)` to the final assert of the named probe fn."""
    i = text.find(f"fn {fn_name}(")
    if i == -1:
        return text
    j = text.find("\nfn ", i)
    if j == -1:
        j = text.find("\nproof fn ", i)
    end = j if j != -1 else len(text)
    seg = text[i:end]
    k = seg.rfind(");")
    if k == -1:
        return text
    seg = seg[:k] + ") by (compute);" + seg[k + 2:]
    return text[:i] + seg + text[end:]


def verify_case(model, case: Case, mode: str, hint_cap: int, rlimits: list,
                timeout_s: int, try_compute: bool,
                compute_state: dict | None = None,
                deadline: float | None = None) -> dict:
    """Escalation ladder for one case. Returns raw verdict row fields.

    compute_state: shared per-problem dict; after 3 consecutive compute
    timeouts the compute attempt is disabled for the rest of the problem
    (compute either evaluates in seconds or is hopeless for that spec).
    deadline: per-problem wall clock; once passed, aborts to UNDECIDED
    (reason problem_timeout) rather than starting another Verus attempt."""
    row: dict = {"attempts": 0}
    for attempt, rlimit in enumerate(rlimits, start=1):
        eff = _budget_timeout(timeout_s, deadline)
        if eff is None:
            return {**row, "verdict": "INCONCLUSIVE", "reason": "problem_timeout"}
        rendered = render_harness_auto(model, [case], hint_cap, mode=mode)
        if rendered.gen_errors:
            return {"verdict": "GEN_ERROR", "reason": str(rendered.gen_errors[0][1])[:200],
                    "attempts": attempt}
        with tempfile.TemporaryDirectory() as td:
            f = Path(td) / "case.rs"
            f.write_text(rendered.file_text, encoding="utf-8")
            r = run_verus(f, rlimit=rlimit, timeout_s=eff)
        row["attempts"] = attempt
        if r.status in ("tool_error", "compile_error", "vir_error"):
            return {**row, "verdict": "GEN_ERROR", "reason": r.status}
        fd = r.func_details
        # NOTE: the in-harness __pre probe is ONE-SIDED — a failure means
        # "couldn't prove", never "provably violates" (only the three-way
        # pre-gate can refute). It feeds pre_proved for confirmation tiering
        # and must not veto the rej/acc verdicts.
        row["pre_proved"] = row.get("pre_proved") or bool(fd.get("__pre_neg_0"))
        rej = fd.get("__rej_neg_0")
        acc = fd.get("__acc_neg_0")
        if rej and acc:
            return {**row, "verdict": "HARNESS_SUSPECT"}
        if rej:
            return {**row, "verdict": "REJECTED"}
        if acc:
            return {**row, "verdict": "ACCEPTED"}

    # final attempt: `by (compute)` on BOTH post probes (quantifier-free only).
    # Compute decides ground facts the SMT unfolding budget cannot (deep
    # recursion, vstd fns like pow2) — in either polarity, so it can surface
    # an ACCEPTED (incompleteness witness) as well as a REJECTED.
    cs = compute_state if compute_state is not None else {}
    if try_compute and cs.get("consec_timeouts", 0) < 3:
        compute_timeout = int(get("symbolic", "compute_timeout_s", 15))
        eff = _budget_timeout(min(compute_timeout, timeout_s), deadline)
        if eff is None:
            return {**row, "verdict": "INCONCLUSIVE", "reason": "problem_timeout"}
        rendered = render_harness_auto(model, [case], hint_cap, mode=mode)
        if not rendered.gen_errors:
            text = _inject_compute_fn(rendered.file_text, "__rej_neg_0")
            text = _inject_compute_fn(text, "__acc_neg_0")
            with tempfile.TemporaryDirectory() as td:
                f = Path(td) / "case_c.rs"
                f.write_text(text, encoding="utf-8")
                r = run_verus(f, rlimit=(rlimits[-1] if rlimits else 60), timeout_s=eff)
            if r.status == "timeout":
                cs["consec_timeouts"] = cs.get("consec_timeouts", 0) + 1
            else:
                cs["consec_timeouts"] = 0
            if r.status not in ("tool_error", "compile_error", "vir_error"):
                fd = r.func_details
                rej = fd.get("__rej_neg_0")
                acc = fd.get("__acc_neg_0")
                row["attempts"] = row.get("attempts", 0) + 1
                if rej and acc:
                    return {**row, "verdict": "HARNESS_SUSPECT", "strategy": "compute"}
                if rej:
                    return {**row, "verdict": "REJECTED", "strategy": "compute"}
                if acc:
                    return {**row, "verdict": "ACCEPTED", "strategy": "compute"}

    return {**row, "verdict": "INCONCLUSIVE"}


def batch_probe(model, cases: list, mode: str, hint_cap: int, rlimit: float,
                timeout_s: int, deadline: float | None = None) -> list | None:
    """Attempt-1 for a batch of cases in ONE Verus file (rlimit is
    per-function, so budgets don't interact). Returns one dict per case
    (verdict None = undecided, escalate individually), or None when the whole
    batch failed to run — callers then fall back to individual runs so one
    bad literal can't poison neighbours."""
    eff = _budget_timeout(timeout_s, deadline)
    if eff is None:
        return None
    rendered = render_harness_auto(model, cases, hint_cap, mode=mode)
    per_case_err = dict(rendered.gen_errors)
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "batch.rs"
        f.write_text(rendered.file_text, encoding="utf-8")
        r = run_verus(f, rlimit=rlimit, timeout_s=eff)
    if r.status in ("tool_error", "compile_error", "vir_error", "timeout"):
        return None
    fd = r.func_details
    out: list[dict] = []
    for i in range(len(cases)):
        if i in per_case_err:
            out.append({"verdict": "GEN_ERROR",
                        "reason": str(per_case_err[i])[:200], "attempts": 1})
            continue
        row = {"attempts": 1, "pre_proved": bool(fd.get(f"__pre_neg_{i}"))}
        rej = fd.get(f"__rej_neg_{i}")
        acc = fd.get(f"__acc_neg_{i}")
        if rej and acc:
            row["verdict"] = "HARNESS_SUSPECT"
        elif rej:
            row["verdict"] = "REJECTED"
        elif acc:
            row["verdict"] = "ACCEPTED"
        else:
            row["verdict"] = None
        out.append(row)
    return out

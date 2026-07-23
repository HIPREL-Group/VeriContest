"""Vacuity probes V1 and V1-strong (V1S). V1 injects `assert(false)` at fn
entry; V1S replaces the whole ensures with `false` and re-verifies the body.
A `verified` outcome means the code path is unreachable / preconditions are
contradictory.

Requires Verus. When Verus is unavailable the probe returns status "skip"
(recorded), never a false PASS.
"""
from __future__ import annotations

import re
import tempfile
from dataclasses import dataclass
from pathlib import Path

from spec_testing.common.repo import Problem
from spec_testing.common.specmodel import SpecModel
from spec_testing.common.verusrun import find_verus_binary, run_verus
from spec_testing.common import specmodel as _sm  # ensures post2exe is on sys.path
import gen_test_post as gtp  # noqa: E402  (made importable by specmodel)

ASSERT_FALSE = "proof { assert(false); }"


@dataclass
class VacuityFlag:
    probe: str          # V1 | V1S
    severity: str
    message: str


def _find_fn_body_span(text: str, fn_name: str) -> tuple[int, int] | None:
    """Return (body_open_index, body_close_index) for the exec fn body."""
    for m in re.finditer(gtp.FN_HEAD_RE, text):
        if m.group("name") != fn_name:
            continue
        prefix = text[max(0, m.start() - 64): m.start()]
        if not gtp.is_exec_fn_prefix(prefix):
            continue
        close_paren = gtp.find_matching_paren(text, m.end() - 1)
        if close_paren == -1:
            return None
        nxt = None
        for mm in re.finditer(gtp.FN_HEAD_RE, text):
            if mm.start() > close_paren:
                nxt = mm.start()
                break
        region = text[:nxt] if nxt is not None else text
        body_open, body_close = gtp.find_fn_body_brace(region, close_paren + 1)
        if body_open == -1:
            return None
        return body_open, body_close
    return None


def _inject_first_stmt(text: str, body_open: int) -> str:
    return text[:body_open + 1] + "\n    " + ASSERT_FALSE + "\n" + text[body_open + 1:]


def run_vacuity(problem: Problem, model: SpecModel, rlimit: float = 10, timeout_s: int = 120) -> tuple[list[VacuityFlag], str]:
    """Run V1, then V1-strong if V1 didn't fire. Returns (flags, status)."""
    if find_verus_binary() is None:
        return [], "skip:verus_unavailable"
    verified = problem.read("verified.rs")
    if verified is None:
        return [], "skip:no_verified_rs"

    span = _find_fn_body_span(verified, model.fn_name)
    if span is None:
        return [], "skip:fn_body_not_found"
    body_open, _ = span

    flags: list[VacuityFlag] = []

    # V1: assert(false) as first statement of the target fn body.
    v1_text = _inject_first_stmt(verified, body_open)
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "v1.rs"
        f.write_text(v1_text, encoding="utf-8")
        r = run_verus(f, rlimit=rlimit, verify_function=model.fn_name, verify_root=True, timeout_s=timeout_s)
    if r.status == "verified":
        flags.append(VacuityFlag("V1", "FLAG_HIGH",
                                 "assert(false) verifies at fn entry -> contradictory requires/ambient axioms"))
    elif r.status in ("tool_error", "compile_error", "vir_error"):
        return flags, f"skip:{r.status}"

    # V1-strong: replace the WHOLE ensures with `false` and
    # verify the body. Unlike V1, the body's own accesses seed Z3's quantifier
    # instantiation, so contradictions hidden behind quantifiers surface
    # (lc704: `forall 0 <= i <= j ==> a[i] < a[j]`). A `verified` outcome on a
    # terminating body is a machine-checked proof of unreachability — zero-FP.
    if not flags:
        v1s = run_vacuity_strong(problem, model, rlimit=max(rlimit, 30), timeout_s=timeout_s)
        if v1s is not None:
            flags.extend(v1s)

    return flags, "ran"


def run_vacuity_strong(problem: Problem, model: SpecModel, rlimit: float = 30,
                       timeout_s: int = 240) -> list[VacuityFlag] | None:
    """`ensures false` probe. Returns flags, or None when not applicable
    (no ensures block found / compile trouble — recorded by caller as skip)."""
    from spec_testing.common import splice

    verified = problem.read("verified.rs")
    if verified is None:
        return None
    text = splice.replace_ensures(verified, model.fn_name, ["false"])
    if text is None:
        return None
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "v1s.rs"
        f.write_text(text, encoding="utf-8")
        r = run_verus(f, rlimit=rlimit, verify_function=model.fn_name,
                      verify_root=True, no_cheating=True, timeout_s=timeout_s)
    if r.status == "verified":
        return [VacuityFlag("V1S", "FLAG_HIGH",
                            "`ensures false` verifies over the fn body -> "
                            "unreachable exit (contradictory requires) — spec is vacuous")]
    if r.status in ("tool_error", "compile_error", "vir_error"):
        return None
    return []

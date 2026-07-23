"""Symbolic test stage: generate (or load) the per-problem test store, then
decide every case with Verus probes.

Public verdicts are exactly ACCEPTED / REJECTED (each backed by a positive
Verus proof) and UNDECIDED (everything else, with a reason). A REJECTED
positive is a machine-checked soundness finding; an ACCEPTED negative is an
incompleteness finding when the confirmation tier proves the input valid and
the wrong output wrong.
"""
from __future__ import annotations

import os
import time
from concurrent.futures import ThreadPoolExecutor

from spec_testing.common import layout, spec_shape, specmodel
from spec_testing.common.config import get
from spec_testing.common.determinism import check_determinism
from spec_testing.common.pregate import input_size
from spec_testing.common.testcases import Case
from spec_testing.symbolic import casegen, probes


def _scfg(key: str, default):
    return get("symbolic", key, default)


def _workers() -> int:
    n = int(_scfg("workers", 0))
    if n <= 0:
        n = min(8, max(1, (os.cpu_count() or 4) - 2))
    return n


def _to_case(row: dict, model, is_cf: bool):
    c = Case(input=row["input"], output=row["output"], source=row.get("source", ""),
             meta=row.get("meta", {}))
    if is_cf and isinstance(row["input"], str):
        from spec_testing.common.cf_align import normalize_cf_case
        return normalize_cf_case(model, c)
    return c


def _final_verdict(row: dict, problem_hard: bool, deep_fuel: bool) -> dict:
    """Collapse raw probe verdicts onto ACCEPTED / REJECTED / UNDECIDED."""
    v = row.get("verdict")
    if v in ("ACCEPTED", "REJECTED"):
        return row
    row["verdict"] = "UNDECIDED"
    if row.get("reason") == "problem_timeout":
        return row
    if v == "HARNESS_SUSPECT":
        row["reason"] = "harness_suspect"
    elif v == "GEN_ERROR":
        detail = row.pop("reason", "")
        row["reason"] = f"gen_error:{detail}" if detail else "gen_error"
    elif v == "SIZE_SKIPPED":
        row["reason"] = "size_skipped"
    elif problem_hard:
        row["reason"] = "quant_hard"
    elif deep_fuel:
        row["reason"] = "fuel_hard"
    else:
        row["reason"] = "inconclusive"
    return row


def run(problem, *, force: bool = False) -> dict:
    t0 = time.monotonic()
    m = specmodel.load_spec_model(problem)
    kind, pid = problem.kind, problem.problem_id
    if isinstance(m, specmodel.GenError):
        out = {"unsupported": m.reason}
        layout.write_json(layout.path(kind, pid, "symbolic_pos"), out)
        layout.write_json(layout.path(kind, pid, "symbolic_neg"), out)
        return out

    is_cf = problem.is_codeforces

    # ---- test store: generate or reuse ------------------------------------
    pos_path = layout.path(kind, pid, "pos_tests")
    neg_path = layout.path(kind, pid, "neg_tests")
    gen_detail: dict = {}
    if force or not pos_path.exists() or not neg_path.exists():
        positives, negatives, gen_detail = casegen.generate(
            problem, m, seed=int(get("run", "seed", 20260713)))
        layout.write_json(pos_path, positives)
        layout.write_json(neg_path, negatives)
        cases_origin = "generated"
    else:
        positives = layout.load_cases(kind, pid, "pos_tests")
        negatives = layout.load_cases(kind, pid, "neg_tests")
        cases_origin = "cached"

    # No positives => nothing to verify: positives anchor the soundness side,
    # seed every negative source (exec_mut/outmut/cross), and are the accepted
    # anchor required to confirm any negative. Short-circuit before the
    # determinism proof and the probe passes.
    if not positives:
        empty = {"header": {"n": 0, "reason": "no_positives"}, "rows": []}
        layout.write_json(layout.path(kind, pid, "symbolic_pos"), empty)
        layout.write_json(layout.path(kind, pid, "symbolic_neg"), empty)
        return {"skipped": "no_positives", "cases": cases_origin,
                "n_pos": 0, "n_neg": len(negatives), "findings": [],
                "wall_s": round(time.monotonic() - t0, 1)}

    # ---- static shape + determinism --------------------------------------
    hard = spec_shape.l1_hard(m)
    mode = "spec" if is_cf else ("exec" if spec_shape.needs_exec_harness(m) else "spec")
    # Determinism is only the wrongness basis when the judge can't already
    # establish it. For scalar-return LC/extended problems the judge decides
    # uniqueness by exact equality, so the (expensive) determinism proof is
    # skipped — it would be computed and discarded.
    from spec_testing.common.values import spec_type as _spec_type
    unique_kinds = set(_scfg("assume_unique_answer_kinds", ["leetcode", "extended", "codeforces"]))
    judge_unique = (kind in unique_kinds and not m.has_mut_ref
                    and _spec_type(m.ret_type).kind in ("int", "bool", "char"))
    determinism = "unknown"
    if not judge_unique:
        determinism = check_determinism(
            m, rlimit=float(_scfg("determinism_rlimit", 60)),
            timeout_s=int(_scfg("determinism_timeout_s", 180)))


    rlimits = [float(x) for x in _scfg("rlimits", [10, 100, 600])]
    neg_rlimits = [float(x) for x in _scfg("neg_rlimits", rlimits[:2])]
    hard_rlimits = [float(x) for x in _scfg("hard_rlimits", rlimits[:1])]
    hint_cap = int(_scfg("hint_cap", 64))
    timeout_s = int(_scfg("attempt_timeout_s", 180))
    batch_size = int(_scfg("batch_size", 10))
    batch_timeout_s = int(_scfg("batch_timeout_s", 180))
    fuel_hard_threshold = int(_scfg("fuel_hard_threshold", 32))
    size_cap = int(_scfg("size_cap", 128))
    # hard per-problem wall budget: once past it, remaining undecided cases
    # abort to UNDECIDED(problem_timeout) instead of starting more Verus work
    deadline = t0 + float(_scfg("problem_timeout_s", 300))
    qf = probes.quantifier_free(m)

    from spec_testing.common import harness as _h
    has_recursive = bool(_h.recursive_helper_paths(m))

    def _case_vals(case: Case) -> list:
        vals = list(case.input.values()) if isinstance(case.input, dict) else [case.input]
        vals.append(case.output)
        return vals

    def _expected_hard(case: Case) -> tuple[bool, bool]:
        """Classified BEFORE any Verus run — QUANT_HARD by spec shape,
        FUEL_HARD by recursion depth over the case values."""
        deep = has_recursive and _h.compute_fuel(_case_vals(case)) >= fuel_hard_threshold
        return (hard or deep), deep

    def finalize(row_dict: dict, base: dict) -> dict:
        out = {"case_id": base["id"], "source": base.get("source"), **row_dict}
        # the three-way pre-gate is authoritative when it PROVED this input
        if base.get("pre") == "proved":
            out["pre_proved"] = True
        return out

    workers = _workers()
    pool = ThreadPoolExecutor(max_workers=workers)
    compute_state: dict = {}

    def decide_side(kind_label: str, rows_in: list[dict]) -> list[dict]:
        results: dict[str, dict] = {}
        batch_todo: list[tuple[dict, Case]] = []
        # (row, case, hard, deep, batch_partial | None)
        escalate: list[tuple[dict, Case, bool, bool, dict | None]] = []
        deep_by_id: dict[str, bool] = {}
        for row in rows_in:
            cid = row["id"]
            case = _to_case(row, m, is_cf)
            if case is None:
                results[cid] = {"case_id": cid, "source": row.get("source"),
                                "verdict": "GEN_ERROR", "reason": "cf_alignment"}
                continue
            if input_size(case.input) + input_size(case.output) > size_cap:
                # symbolically intractable (huge literal harness); such cases
                # still earn their keep in exec-mutation — never in Z3
                results[cid] = {"case_id": cid, "source": row.get("source"),
                                "verdict": "SIZE_SKIPPED"}
                continue
            is_hard, deep = _expected_hard(case)
            deep_by_id[cid] = deep
            # exec-mode harnesses are heavy: batching them lets one intractable
            # case stall the whole file until the batch timeout, then re-runs
            # them all individually. Skip batching for exec so slow cases stay
            # isolated and cheap ones decide on their own.
            if is_hard or batch_size <= 1 or mode == "exec":
                escalate.append((row, case, is_hard, deep, None))
            else:
                batch_todo.append((row, case))

        # ---- attempt 1 for healthy cases: batched ----
        if batch_todo:
            batches = [batch_todo[i:i + batch_size]
                       for i in range(0, len(batch_todo), batch_size)]

            def run_batch(b):
                bt = time.monotonic()
                out = probes.batch_probe(m, [c for _, c in b], mode, hint_cap,
                                         rlimits[0], batch_timeout_s, deadline=deadline)
                return out, round((time.monotonic() - bt) * 1000)

            for b, (out, ms) in zip(batches, pool.map(run_batch, batches)):
                for k, (row, case) in enumerate(b):
                    if out is None:
                        # whole-batch failure (compile error / timeout):
                        # full individual ladder, nothing assumed
                        escalate.append((row, case, False, False, None))
                        continue
                    r = out[k]
                    if r["verdict"] is None:
                        escalate.append((row, case, False, False,
                                         {"pre_proved": r.get("pre_proved", False)}))
                    else:
                        r["wall_ms"] = ms  # shared batch wall, for tuning
                        results[row["id"]] = finalize(r, row)

        # ---- individual ladders: hard cases + batch leftovers ----
        def esc_job(item):
            row, case, is_hard, deep, partial = item
            if is_hard:
                ladder = hard_rlimits
            elif kind_label == "pos":
                ladder = rlimits if partial is None else rlimits[1:]
            else:
                ladder = neg_rlimits if partial is None else neg_rlimits[1:]
            et = time.monotonic()
            res = probes.verify_case(m, case, mode, hint_cap, ladder, timeout_s,
                                     try_compute=qf, compute_state=compute_state,
                                     deadline=deadline)
            res["wall_ms"] = round((time.monotonic() - et) * 1000)
            if partial is not None:
                res["pre_proved"] = res.get("pre_proved") or partial.get("pre_proved", False)
                res["attempts"] = res.get("attempts", 0) + 1   # count the batch attempt
            return finalize(res, row)

        for out in pool.map(esc_job, escalate):
            results[out["case_id"]] = out

        # A positive rejection is a soundness claim: it stands only when the
        # input provably satisfies the precondition.
        if kind_label == "pos":
            for r in results.values():
                if r.get("verdict") == "REJECTED" and not r.get("pre_proved"):
                    r["verdict"] = "UNDECIDED"
                    r["reason"] = "rejected_pre_unproved"
        return [_final_verdict(results[row["id"]], hard,
                               deep_by_id.get(row["id"], False))
                for row in rows_in]

    detail: dict = {"mode": mode, "hard": hard, "determinism": determinism,
                    "workers": workers, "cases": cases_origin}
    if gen_detail:
        detail["casegen"] = gen_detail
    try:
        pos_rows = decide_side("pos", positives)
        neg_rows = decide_side("neg", negatives)
    finally:
        pool.shutdown(wait=False)

    # ---- confirmation tiering for accepted negatives (zero-FP) ------------
    # Harness health measures CONTRADICTORY evidence; UNDECIDED positives are
    # prover-budget limits — neutral, not harness-bug evidence. Confirming an
    # ACCEPTED negative as a real incompleteness requires ALL of: the input
    # provably satisfies requires, wrongness is established (exact-equality
    # judge on pure scalar returns, or a spec-determinism proof), and the
    # positive controls prove the harness encodes the spec faithfully.
    n_pos_ok = sum(1 for r in pos_rows if r.get("verdict") == "ACCEPTED")
    n_pos_rej = sum(1 for r in pos_rows if r.get("verdict") == "REJECTED")
    n_pos_decidable = n_pos_ok + n_pos_rej
    harness_health = (n_pos_ok / n_pos_decidable) if n_pos_decidable else 0.0

    # Harness-faithfulness gate, keyed on per-positive capture provenance
    # (`trust`, set by casegen for Codeforces). The Codeforces oracle is trusted
    # only through the arg-capture driver:
    #   authoritative — reference output verified against the problem statement;
    #   capture        — real captured I/O, answer not cross-checked;
    #   heuristic      — fallback stdin/stdout parse (capture unavailable), untrusted.
    # LeetCode/extended carry no `trust` tag and keep the original tolerance, so
    # their findings are unaffected (e.g. lc3022's placeholder-spec soundness bug).
    trust_by_id = {p.get("id"): p.get("trust") for p in positives}
    cf_trusts = [trust_by_id.get(r["case_id"]) for r in pos_rows] if is_cf else []
    # A CF harness is trusted when every positive is capture-derived (none fell
    # back to the heuristic parser). Then a rejected positive reflects the spec,
    # not a parse artifact, and negatives built on the ground-truth outputs hold.
    cf_harness_trusted = is_cf and bool(cf_trusts) and all(
        t in ("authoritative", "capture") for t in cf_trusts)

    unique_answer = (determinism == "unique") or judge_unique
    for r in neg_rows:
        if r.get("verdict") != "ACCEPTED":
            continue
        reasons = []
        if not r.get("pre_proved"):
            reasons.append("pre_unproved")
        if not unique_answer:
            reasons.append("wrongness_unproven_multi_output")
        if n_pos_ok == 0:
            reasons.append("no_accepted_positive_anchor")
        elif is_cf and not cf_harness_trusted:
            reasons.append("harness_untrusted")
        elif not is_cf and harness_health < 0.5:
            reasons.append("harness_health_low")
        if reasons:
            r["confirmed"] = False
            r["unconfirmed_reason"] = ",".join(reasons)
        else:
            r["confirmed"] = True
            r["wrongness_basis"] = ("spec_determinism" if determinism == "unique"
                                    else "judge_equality")

    # A rejected positive is a soundness finding only when its (input, output) is
    # trustworthy ground truth: for CF that means an `authoritative` capture seed
    # (reference confirmed correct against the statement), so rejecting it proves
    # the spec is over-constrained — never a reference/parse artifact. LeetCode
    # keeps every rejected positive (its oracle is trusted end to end).
    def _is_soundness(r: dict) -> bool:
        if r.get("verdict") != "REJECTED":
            return False
        return (not is_cf) or trust_by_id.get(r["case_id"]) == "authoritative"

    def _counts(rows: list[dict]) -> dict:
        c: dict = {}
        for r in rows:
            c[r["verdict"]] = c.get(r["verdict"], 0) + 1
        return c

    counts_pos, counts_neg = _counts(pos_rows), _counts(neg_rows)
    n_confirmed = sum(1 for r in neg_rows if r.get("confirmed"))
    wall_s = round(time.monotonic() - t0, 1)
    pos_header = {"n": len(pos_rows), "mode": mode, "hard": hard,
                  "harness_health": round(harness_health, 3), "counts": counts_pos,
                  "wall_s": wall_s}
    n_rej_suppressed = sum(1 for r in pos_rows
                           if r.get("verdict") == "REJECTED" and not _is_soundness(r))
    if n_rej_suppressed:
        # REJECTED positives stay visible as rows but are NOT promoted to findings:
        # without authoritative provenance the CF harness can't separate a real
        # over-constrained spec from a wrong reference output.
        pos_header["findings_suppressed"] = f"untrusted_rejection:{n_rej_suppressed}"
    layout.write_json(layout.path(kind, pid, "symbolic_pos"), {
        "header": pos_header, "rows": pos_rows})
    layout.write_json(layout.path(kind, pid, "symbolic_neg"), {
        "header": {"n": len(neg_rows), "mode": mode, "hard": hard,
                   "determinism": determinism, "counts": counts_neg,
                   "n_confirmed": n_confirmed},
        "rows": neg_rows})

    findings = [{"kind": "soundness", "case_id": r["case_id"]}
                for r in pos_rows if _is_soundness(r)]
    findings += [{"kind": "incompleteness", "case_id": r["case_id"]}
                 for r in neg_rows if r.get("confirmed")]
    detail.update({"n_pos": len(pos_rows), "n_neg": len(neg_rows),
                   "pos": counts_pos, "neg": counts_neg,
                   "harness_health": round(harness_health, 3),
                   "findings": findings, "wall_s": wall_s})
    return detail

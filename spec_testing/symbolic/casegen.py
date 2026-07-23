"""Deterministic per-problem test-case generation.

Positives: description seeds (reconciled against the reference driver) plus
typed mutations of the seeds, gated by schema, dedupe, reference execution,
and the three-way precondition gate. Negatives: code-mutant outputs on the
positive inputs (exec_mut), typed output mutation (outmut), and cross-case
outputs (cross), deduped with balanced per-source caps.
"""
from __future__ import annotations

import json
import os
import random
import shutil
import subprocess

from spec_testing.common import pregate
from spec_testing.common.config import SPEC_TESTING_DIR, get
from spec_testing.testgen import code_mutators
from spec_testing.testgen import driver as driver_mod
from spec_testing.testgen import inputgen
from spec_testing.testgen import seeds as seeds_mod
from spec_testing.testgen.codegen import build_lc_main
from spec_testing.testgen.negatives import gen_negatives
from spec_testing.testgen.validate import Deduper, gate_schema

WORK = SPEC_TESTING_DIR / "work" / "symbolic"


def _tcfg(key: str, default):
    return get("testgen", key, default)


def _ckey(input_obj, output=None) -> str:
    if output is None:
        return json.dumps(input_obj, sort_keys=True, default=str)
    return json.dumps({"i": input_obj, "o": output}, sort_keys=True, default=str)


def _norm_case(row: dict, idx: int, prefix: str) -> dict:
    return {"id": row.get("id") or f"{prefix}:{idx}", "input": row["input"],
            "output": row["output"], "source": row.get("source", prefix),
            "meta": row.get("meta", {}),
            **({"pre": row["pre"]} if "pre" in row else {}),
            **({"trust": row["trust"]} if "trust" in row else {})}


def _shape_sig(input_obj: dict) -> tuple:
    """Coarse shape signature for diversity: container lengths + scalar
    magnitude buckets. Two inputs with the same signature are 'the same kind
    of test' (e.g. two random length-1 arrays)."""
    sig = []
    for k in sorted(input_obj):
        v = input_obj[k]
        if isinstance(v, (list, str)):
            sig.append((k, "len", len(v)))
        elif isinstance(v, bool):
            sig.append((k, "bool", v))
        elif isinstance(v, int):
            sig.append((k, "mag", 0 if v == 0 else (v.bit_length() * (1 if v > 0 else -1))))
        else:
            sig.append((k, "other", str(type(v).__name__)))
    return tuple(sig)


def _n_workers() -> int:
    return min(8, max(1, (os.cpu_count() or 4) - 2))


def _capture_seeds(problem, model, cap_drv, dedup) -> list[dict]:
    """Codeforces ground-truth seeds: the exact typed (input, output) the
    reference main() feeds the verified fn, captured from each raw
    description-example stdin (correct for digit/char representations and
    multi-output mains; multi-test-case examples yield one seed per case).

    `trust` records provenance for the finding gate: "authoritative" when the
    reference reproduced the example's expected output (problem-statement ground
    truth — a spec that rejects it is a genuine soundness bug), else "capture"
    (the reference ran, but its answer wasn't cross-checked against the statement)."""
    pos_seed: list[dict] = []
    for pair in driver_mod.capture_seed_pairs(cap_drv, problem):
        if dedup.check(pair["input"]).ok:
            pos_seed.append({"input": pair["input"], "output": pair["output"],
                             "source": "seed", "meta": {},
                             "trust": "authoritative" if pair.get("authoritative") else "capture"})
    return pos_seed


def _ref_output(problem, model, drv, cap_drv, inp):
    """Reference output for a typed input. Codeforces: serialize -> capture, and
    only accept when the captured input round-trips exactly (else the heuristic
    stdin serialization diverged from the real main() and the pair is untrusted
    -> None, never a fabricated positive). LeetCode: the normal JSON driver."""
    if problem.is_codeforces and cap_drv is not None and cap_drv.build_ok:
        from spec_testing.common import cf_io
        try:
            stdin_text = cf_io.build_stdin_generic(model, inp)
        except Exception:
            return None
        for pair in driver_mod.run_capture(cap_drv, stdin_text):
            if pair.get("input") == inp:
                return pair.get("output")
        return None
    rr = driver_mod.run_case(drv, problem, inp, model=model)
    return rr.output if rr.ok else None


def _reconcile_seeds(problem, model, drv, dedup, is_cf: bool) -> tuple[list[dict], int]:
    """Description examples gated by schema + dedupe, reconciled against the
    reference driver. A seed whose stated output disagrees with the reference
    is dropped (the driver output is the canonical form)."""
    sr = seeds_mod.extract_seeds(problem, model if not is_cf else None)
    pos_seed: list[dict] = []
    mismatch = 0
    for s in sr.seeds:
        if not is_cf and isinstance(s.input, dict) and not gate_schema(s.input, model).ok:
            continue
        if not dedup.check(s.input).ok:
            continue
        out = s.output
        if drv.build_ok:
            rr = driver_mod.run_case(drv, problem, s.input)
            if rr.ok:
                # component-aware match: &mut drivers return a composite
                # {ret, <p>_after} while description seeds carry just the ret
                same = (rr.output == s.output or
                        (isinstance(rr.output, dict) and not isinstance(s.output, dict)
                         and rr.output.get("ret") == s.output))
                if not same:
                    mismatch += 1
                    continue
                out = rr.output
        pos_seed.append({"input": s.input, "output": out, "source": "seed", "meta": {}})
    return pos_seed, mismatch


def _select_diverse(cand_inputs: list[dict], model, dedup, drv, problem,
                    quota: int, ref_out=None) -> tuple[list[dict], dict]:
    """Positive selection preferring candidates whose input shape AND whose
    reference output are not yet represented (shape diversity alone lets many
    inputs share one answer — e.g. profit 0 — which starves the cross/exec
    negative sources of distinct wrong values). Deferred same-output
    candidates keep their computed output and only fill leftover quota."""
    from concurrent.futures import ThreadPoolExecutor
    from spec_testing.common.pregate import input_size

    seen_shapes: set[tuple] = set()
    out_counts: dict[str, int] = {}
    picked: list[dict] = []
    deferred: list[dict] = []
    stats = {"driver_fail": 0, "gate_fail": 0, "dup": 0, "output_deferred": 0,
             "oversize_skipped": 0}
    # Oversize inputs are dead weight symbolically (size-skipped downstream,
    # unknown at the pre-gate => can never anchor a confirmed finding); keep
    # exactly `stress_slots` of them for exec-mutation crash coverage.
    sym_cap = int(get("symbolic", "size_cap", 128))
    stress_slots = int(_tcfg("gen_stress_slots", 1))
    oversize_taken = 0

    # Precompute reference outputs in parallel for every gate-passing unique
    # input — each pick becomes a cache lookup instead of a subprocess run.
    unique_inputs: dict[str, dict] = {}
    for inp in cand_inputs:
        if isinstance(inp, dict) and gate_schema(inp, model).ok:
            unique_inputs.setdefault(_ckey(inp), inp)

    def _out(i):
        if ref_out is not None:
            return ref_out(i)
        rr = driver_mod.run_case(drv, problem, i, model=model)
        return rr.output if rr.ok else None

    out_cache: dict[str, object] = {}   # _ckey -> reference output, or None on failure
    if unique_inputs:
        with ThreadPoolExecutor(max_workers=_n_workers()) as dpool:
            for k, out in zip(unique_inputs, dpool.map(_out, unique_inputs.values())):
                out_cache[k] = out

    def _okey(output) -> str:
        return json.dumps(output, sort_keys=True, default=str)

    queue = [inp for inp in cand_inputs if isinstance(inp, dict)]
    for prefer_fresh_shape in (True, False):
        remaining: list[dict] = []
        for inp in queue:
            if len(picked) >= quota:
                remaining.append(inp)
                continue
            if prefer_fresh_shape and _shape_sig(inp) in seen_shapes:
                remaining.append(inp)
                continue
            oversize = input_size(inp) > sym_cap
            if oversize and oversize_taken >= stress_slots:
                stats["oversize_skipped"] += 1
                continue
            if not gate_schema(inp, model).ok:
                stats["gate_fail"] += 1
                continue
            if not dedup.check(inp).ok:
                stats["dup"] += 1
                continue
            ckey = _ckey(inp)
            out = out_cache[ckey] if ckey in out_cache else _out(inp)
            if out is None:
                stats["driver_fail"] += 1
                continue
            row = {"input": inp, "output": out, "source": "gen", "meta": {}}
            if prefer_fresh_shape and out_counts.get(_okey(out), 0) >= 2:
                deferred.append(row)          # over-represented answer
                stats["output_deferred"] += 1
                continue
            out_counts[_okey(out)] = out_counts.get(_okey(out), 0) + 1
            seen_shapes.add(_shape_sig(inp))
            if oversize:
                oversize_taken += 1
            picked.append(row)
        queue = remaining

    for row in deferred:                      # fill leftover quota
        if len(picked) >= quota:
            break
        if pregate.input_size(row["input"]) > sym_cap:
            if oversize_taken >= stress_slots:
                stats["oversize_skipped"] += 1
                continue
            oversize_taken += 1
        picked.append(row)
    return picked, stats


def _apply_pregate_and_fill(model, pos_seed: list[dict], pos_gen: list[dict],
                            is_cf: bool, detail: dict) -> list[dict]:
    """Three-way precondition gate + fill policy: refuted inputs are never
    stored; seeds are otherwise always kept; generated rows fill with PROVED
    first up to n_pos_max, then UNKNOWN only below the n_pos_min floor."""
    n_min = int(_tcfg("n_pos_min", 8))
    n_max = int(_tcfg("n_pos_max", 10))
    if is_cf and (pos_seed + pos_gen) and isinstance((pos_seed + pos_gen)[0]["input"], str):
        for p in pos_seed + pos_gen:
            p["pre"] = "unknown"
        return (pos_seed + pos_gen)[:n_max]


    all_pos = pos_seed + pos_gen
    rep = pregate.check_inputs(model, [p["input"] for p in all_pos],
                               rlimit=float(get("pregate", "rlimit", 30)),
                               batch_size=int(get("pregate", "batch", 8)),
                               size_cap=int(get("pregate", "size_cap", 256)))
    kept_seed: list[dict] = []
    gen_proved: list[dict] = []
    gen_unknown: list[dict] = []
    seed_refuted = 0
    dropped_inputs: list[str] = []
    for i, p in enumerate(all_pos):
        verdict = rep.per_input.get(i, "unknown") if rep.available else "unknown"
        p["pre"] = "proved" if verdict == "proved" else "unknown"
        if verdict in ("refuted", "contradictory"):
            dropped_inputs.append(json.dumps(p["input"], default=str)[:160])
            if p["source"] == "seed":
                seed_refuted += 1
            continue
        if p["source"] == "seed":
            kept_seed.append(p)
        elif p["pre"] == "proved":
            gen_proved.append(p)
        else:
            gen_unknown.append(p)

    positives = (kept_seed + gen_proved)[:n_max]   # seeds first, capped at n_max
    if len(positives) < n_min:
        positives += gen_unknown[:n_min - len(positives)]

    detail["pre_gate_mode"] = rep.mode if rep.available else "skip"
    detail["pre_refuted"] = len(dropped_inputs)
    detail["pre_unknown"] = sum(1 for p in positives if p["pre"] == "unknown")
    if dropped_inputs:
        detail["pre_dropped_inputs"] = dropped_inputs
    if seed_refuted:
        detail["seed_pre_refuted"] = seed_refuted
    return positives


def _exec_mut(problem, model, positives: list[dict], seed: int,
              is_cf: bool) -> tuple[list[dict], dict]:
    """Code-mutant negatives: build up to n_code_mutants mutants (drawn from a
    4x pool — fallback mutants often fail to compile), run each on every
    positive input, and keep distinct (input, wrong output) pairs."""
    from concurrent.futures import ThreadPoolExecutor

    neg_exec: list[dict] = []
    stats = {"built": 0, "compile_fail": 0, "crash": 0, "behavior_same": 0,
             "runs": 0, "differing": 0, "distinct_pairs": 0}
    code = problem.read("main.rs" if is_cf else "code.rs")
    if not code:
        return neg_exec, stats
    n_mut = int(_tcfg("n_code_mutants", 10))
    if code_mutators.cargo_mutants_available():
        mutants = code_mutators.generate_cargo_mutants(
            code, WORK / problem.problem_id / "crate", n_mut * 4, seed)
    else:
        mutants = code_mutators.generate_fallback(code, n_mut * 4, seed)

    def _build_one(mut):
        mdir = WORK / problem.problem_id / f"m{mut.idx}"
        mdir.mkdir(parents=True, exist_ok=True)
        if is_cf:
            # Capture-instrument the mutant so we read the exact typed (input,
            # output) it computes — the same ground-truth path as the reference,
            # so a mutant's wrong answer becomes a valid negative on the real
            # typed input (the old str(dict)-on-stdin path never parsed).
            b = driver_mod.build_capture_driver(problem, mdir, model, main_override=mut.text)
            return mut, (b if b.build_ok else None)
        (mdir / "main.rs").write_text(build_lc_main(mut.text, model), encoding="utf-8")
        ok = _compile(mdir / "main.rs", mdir / "driver.exe")
        return mut, (mdir / "driver.exe") if ok else None

    n_workers = _n_workers()
    built: list[tuple] = []
    idx = 0
    with ThreadPoolExecutor(max_workers=n_workers) as cpool:
        while len(built) < n_mut and idx < len(mutants):
            wave = mutants[idx: idx + max(n_workers, n_mut - len(built))]
            idx += len(wave)
            for mut, exe in cpool.map(_build_one, wave):
                if exe is None:
                    stats["compile_fail"] += 1
                elif len(built) < n_mut:
                    built.append((mut, exe))
    stats["built"] = len(built)

    # a mutant that times out twice in a row is a runaway (infinite loop) —
    # every further run would burn the full timeout and never yield negatives
    def _run_all(item):
        mut, exe = item
        local = {"runs": 0, "crash": 0, "differing": 0}
        diffs: list[tuple] = []
        consec_to = 0
        for p in positives:               # seeds first: positives is seed+gen
            local["runs"] += 1
            rr = _run_mutant(exe, problem, p["input"], model)
            if rr is _TIMEOUT:
                local["crash"] += 1
                consec_to += 1
                if consec_to >= 2:
                    break
                continue
            consec_to = 0
            if rr is None:
                local["crash"] += 1
                continue
            if rr == p["output"]:
                continue
            local["differing"] += 1
            diffs.append((p, rr))
        return mut, local, diffs

    seen_pairs: set[str] = set()
    with ThreadPoolExecutor(max_workers=n_workers) as rpool:
        results = list(rpool.map(_run_all, built))
    for mut, local, diffs in results:     # deterministic order preserved
        for k in ("runs", "crash", "differing"):
            stats[k] += local[k]
        if not diffs:
            stats["behavior_same"] += 1
            continue
        for p, rr in diffs:
            key = _ckey(p["input"], rr)
            if key in seen_pairs:
                continue
            seen_pairs.add(key)
            stats["distinct_pairs"] += 1
            neg_exec.append({"input": p["input"], "output": rr,
                             "source": "exec_mut",
                             "meta": {"mutant": mut.idx, "op": mut.op,
                                      "pos_id": p["id"]}})
    # seed inputs are the highest-value tests: keep their pairs first when
    # the per-source cap trims
    neg_exec.sort(key=lambda n: 0 if str(n["meta"].get("pos_id", "")).startswith("seed") else 1)
    return neg_exec, stats


def _interleave_by_input(rows: list[dict]) -> list[dict]:
    """Round-robin rows across their input (one per positive per round) so a
    per-source cap samples every positive instead of exhausting the first."""
    groups: dict[str, list[dict]] = {}
    for n in rows:
        groups.setdefault(_ckey(n["input"]), []).append(n)
    out: list[dict] = []
    queues = list(groups.values())
    while queues:
        queues = [q for q in queues if q]
        for q in queues:
            if q:
                out.append(q.pop(0))
    return out


def _dedupe_and_cap(neg_exec: list[dict], neg_outmut: list[dict],
                    neg_cross: list[dict], positives: list[dict],
                    detail: dict) -> list[dict]:
    """Structural dedupe + equals-correct guard, per-source caps in priority
    order exec_mut > outmut > cross, backfill past the caps up to neg_max
    when the total lands below neg_min."""
    neg_min = int(_tcfg("neg_min", 20))
    neg_max = int(_tcfg("neg_max", 30))
    caps = {"exec_mut": int(_tcfg("neg_cap_exec_mut", 15)),
            "outmut": int(_tcfg("neg_cap_outmut", 10)),
            "cross": int(_tcfg("neg_cap_cross", 8))}
    by_source = {"exec_mut": neg_exec,
                 "outmut": _interleave_by_input(neg_outmut),
                 "cross": neg_cross}
    correct_pairs = {_ckey(p["input"], p["output"]) for p in positives}

    seen: set[str] = set()
    kept: dict[str, list[dict]] = {k: [] for k in by_source}
    overflow: dict[str, list[dict]] = {k: [] for k in by_source}
    total = 0
    dropped = {"dup": 0, "equals_correct": 0, "cap": 0}
    for src in ("exec_mut", "outmut", "cross"):
        for n in by_source[src]:
            key = _ckey(n["input"], n["output"])
            if key in seen:
                dropped["dup"] += 1
                continue
            if key in correct_pairs:
                dropped["equals_correct"] += 1
                continue
            seen.add(key)
            if total >= neg_max or len(kept[src]) >= caps[src]:
                overflow[src].append(n)
                continue
            kept[src].append(n)
            total += 1
    backfilled = 0
    if total < neg_min:                   # backfill past per-source caps
        for src in ("exec_mut", "outmut", "cross"):
            for n in overflow[src]:
                if total >= neg_max:
                    break
                kept[src].append(n)
                total += 1
                backfilled += 1
    dropped["cap"] = sum(len(v) for v in overflow.values()) - backfilled

    # A negative reuses a positive's input, and `requires` depends only on the
    # input — so carry the positive's pregate proof forward. This lets the
    # symbolic stage confirm an ACCEPTED negative without re-proving the
    # precondition via the weaker in-harness probe (still sound, zero-FP).
    proved = {_ckey(p["input"]) for p in positives if p.get("pre") == "proved"}
    negatives: list[dict] = []
    for src in ("exec_mut", "outmut", "cross"):
        for i, n in enumerate(kept[src]):
            n["pre"] = "proved" if _ckey(n["input"]) in proved else "unknown"
            negatives.append(_norm_case(n, i, src))
    detail["n_neg"] = total
    detail["neg_by_source"] = {k: len(v) for k, v in kept.items()}
    detail["neg_distinct_wrong"] = {
        k: len({json.dumps(n["output"], sort_keys=True, default=str) for n in v})
        for k, v in kept.items()}
    detail["neg_dropped"] = dropped
    return negatives


def generate(problem, model, *, seed: int) -> tuple[list[dict], list[dict], dict]:
    """Deterministic positives + negatives for one problem.

    Returns (pos_rows, neg_rows, detail) with rows in the stored schema
    {id, input, output, source, meta, pre?}.
    """
    detail: dict = {}
    rng = random.Random(seed)
    is_cf = problem.is_codeforces
    n_max = int(_tcfg("n_pos_max", 10))

    drv = driver_mod.build_driver(problem, WORK / problem.problem_id / "ref",
                                  model if not is_cf else None)
    detail["driver_runnable"] = drv.build_ok
    if not drv.build_ok:
        detail["driver_error"] = drv.error

    # Codeforces: an arg-capture driver yields ground-truth typed (input, output)
    # pairs, sidestepping heuristic stdin/stdout parsing.
    cap_drv = None
    if is_cf:
        cap_drv = driver_mod.build_capture_driver(
            problem, WORK / problem.problem_id / "cap", model)
        detail["capture_runnable"] = cap_drv.build_ok
        if not cap_drv.build_ok:
            detail["capture_error"] = cap_drv.error
    ref_out = (lambda inp: _ref_output(problem, model, drv, cap_drv, inp)) if is_cf else None

    dedup = Deduper()
    if is_cf and cap_drv is not None and cap_drv.build_ok:
        pos_seed = _capture_seeds(problem, model, cap_drv, dedup)
        mismatch = 0
    else:
        pos_seed, mismatch = _reconcile_seeds(problem, model, drv, dedup, is_cf)
        if is_cf:
            # Fallback (capture unavailable): heuristic-parsed I/O is untrusted —
            # a rejected positive may be a parse artifact, not a spec bug.
            for p in pos_seed:
                p["trust"] = "heuristic"
    detail["n_seed"] = len(pos_seed)
    detail["seed_mismatch"] = mismatch

    # typed seed mutations; chained rounds let container lengths drift more
    # than +-1 from the seeds, and constrained-input problems lose many
    # candidates to the pre-gate
    pos_gen: list[dict] = []
    ref_runnable = (cap_drv.build_ok if is_cf else drv.build_ok) if (is_cf or drv.build_ok) else False
    can_mutate = ref_runnable and pos_seed and isinstance(pos_seed[0]["input"], dict)
    if can_mutate:

        base = [p["input"] for p in pos_seed]
        mutated: list[dict] = []
        for _ in range(3):
            mutated += inputgen.mutate_inputs(base + mutated, model, rng, n_max * 2)
        pos_gen, sel_stats = _select_diverse(mutated, model, dedup, drv, problem,
                                             quota=n_max * 2, ref_out=ref_out)  # pre-gate trims
        if is_cf:
            # Generated CF outputs come from capture with an exact input
            # round-trip check, so the (input, output) is real; but the answer
            # isn't cross-checked against the statement, so it can anchor
            # incompleteness yet must not, on its own, ground a soundness claim.
            for p in pos_gen:
                p["trust"] = "capture"
        detail["gen_select"] = sel_stats


    positives = _apply_pregate_and_fill(model, pos_seed, pos_gen, is_cf, detail)
    seeds_first = sorted(positives, key=lambda p: 0 if p["source"] == "seed" else 1)
    si = gi = 0
    for p in seeds_first:
        if p["source"] == "seed":
            p["id"] = f"seed:{si}"
            si += 1
        else:
            p["id"] = f"gen:{gi}"
            gi += 1
    positives = seeds_first
    detail["n_pos"] = len(positives)
    detail["pos_distinct_outputs"] = len({json.dumps(p["output"], sort_keys=True, default=str)
                                          for p in positives})

    neg_exec: list[dict] = []
    mutant_stats: dict = {}
    if drv.build_ok and positives:
        neg_exec, mutant_stats = _exec_mut(problem, model, positives, seed, is_cf)
    detail["mutants"] = mutant_stats

    other = gen_negatives(model, positives, rng,
                          int(_tcfg("k_outmut_per_pos", 8)),
                          int(_tcfg("k_cross", 20)))
    neg_outmut = [n for n in other if n["source"] == "outmut"]
    neg_cross = [n for n in other if n["source"] == "cross"]
    negatives = _dedupe_and_cap(neg_exec, neg_outmut, neg_cross, positives, detail)

    pos_rows = [_norm_case(p, i, "pos") for i, p in enumerate(positives)]
    return pos_rows, negatives, detail


def _compile(src, exe) -> bool:
    rustc = get("paths", "rustc_bin", "auto")
    if not rustc or rustc == "auto" or not os.path.exists(rustc):
        rustc = shutil.which("rustc")
    if rustc is None:
        return False
    try:
        # -O0 (no -O): mutants only run tiny inputs under a 5s cap, so
        # optimization is pointless and unoptimized compiles far faster
        r = subprocess.run([rustc, "--edition=2021", "-o", str(exe), str(src)],
                           capture_output=True, text=True,
                           timeout=int(_tcfg("mutant_build_timeout_s", 120)))
        return r.returncode == 0 and exe.exists()
    except (OSError, subprocess.SubprocessError):
        return False


_TIMEOUT = object()   # sentinel: distinguishes runaway mutants from crashes


def _run_mutant(exe, problem, inp, model=None):
    """Run one code mutant on `inp` and return its typed output (or None on
    crash / non-parse, `_TIMEOUT` on timeout). Codeforces: `exe` is a capture
    DriverBuild — serialize `inp` to stdin, run, and return the output the mutant
    captured for exactly that input (round-trip guard). LeetCode: `exe` is a
    binary reading the JSON case on stdin."""
    if problem.is_codeforces:
        from spec_testing.common import cf_io
        try:
            stdin_text = cf_io.build_stdin_generic(model, inp)
        except Exception:
            return None
        for pair in driver_mod.run_capture(
                exe, stdin_text, timeout_s=int(_tcfg("mutant_run_timeout_s", 5))):
            if pair.get("input") == inp:
                return pair.get("output")
        return None
    try:
        p = subprocess.run([str(exe)], input=json.dumps({"input": inp}),
                           capture_output=True, text=True,
                           timeout=int(_tcfg("mutant_run_timeout_s", 5)))
    except subprocess.TimeoutExpired:
        return _TIMEOUT
    if p.returncode != 0:
        return None
    try:
        return json.loads(p.stdout.strip())
    except json.JSONDecodeError:
        return None

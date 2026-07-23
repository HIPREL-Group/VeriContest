# spec_testing

Specification-adequacy testing for the Verus specs.
For every benchmark problem it reports machine-checked evidence of spec
**unsoundness** (the spec rejects a correct output), **incompleteness** (the
spec accepts a wrong output), and **vacuity** (contradictory preconditions).

## Usage

```bash
# sanity-vacuity-check (static checks, vacuity, seed-precondition)
python -m spec_testing.run_sanity lc121              # console report only
python -m spec_testing.run_sanity lc121 --save       # also write sanity_vacuity.json
python -m spec_testing.run_sanity_batch --kind leetcode --save

# symbolic test (generate the test store, decide every case with Verus)
python -m spec_testing.run_symbolic lc121
python -m spec_testing.run_symbolic lc121 --force    # regenerate everything
python -m spec_testing.run_symbolic_batch --limit 20 --summary summary.json
```

The two stages are independent: neither reads the other's output. Symbolic
runs skip a problem whose `symbolic_pos.json` + `symbolic_neg.json` already
exist (`--force` redoes it, regenerating the test store); a problem with
stored test cases but no verdicts reuses the cases as a cache. Batch sanity
prints one status line per problem (flag details follow flagged ones).

Exit codes (single-problem scripts): `0` clean / no findings, `1` flags or
findings, `2` problem not found, `3` crash or unsupported spec. Batch scripts:
`0` no per-problem errors, `1` otherwise.

## Stages

| stage | what it does |
|---|---|
| `sanity-vacuity-check` | static spec checks S1-S7 (unconstrained result, trivial/tautological ensures, stub helpers, ...), vacuity probes (`assert(false)` at entry and an `ensures false` re-verification of the body), and a seed-precondition check (description examples that provably violate `requires`) |
| `symbolic` | builds the test store — positives from description seeds + typed seed mutation (gated by the reference driver and a three-way precondition gate), negatives from code-mutant execution, typed output mutation, and cross-case outputs — then decides every case with per-case Verus probes, and proves output-determinism to establish the wrongness basis for confirming incompleteness |

Symbolic verdicts are exactly three: **ACCEPTED** and **REJECTED** are each
backed by a positive Verus proof; everything else is **UNDECIDED** (with a
reason). A REJECTED positive is a soundness finding; an ACCEPTED negative is
an incompleteness finding when its confirmation tier holds (precondition
proved, wrongness established, healthy positive controls). A failed proof is
never treated as evidence, so findings carry zero false positives by
construction.

## Output layout

```
spec_testing/results/<kind>/<pid>/
    sanity_vacuity.json   # sanity-vacuity-check report
    pos_tests.json        # final positive cases (seeds first, then generated)
    neg_tests.json        # final negative cases (exec_mut, outmut, cross)
    symbolic_pos.json     # per-case verdicts on positives
    symbolic_neg.json     # per-case verdicts on negatives
```

`spec_testing/work/` holds runtime scratch (driver and mutant builds) and is gitignored. All knobs live
in `spec_testing/config.toml`.

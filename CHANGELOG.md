# Changelog

Notable changes to the VeriContest benchmark. Releases are tagged `vYYYY.MM`;
see [RELEASING.md](RELEASING.md).

Contributors: add a line under **Unreleased** in your PR, naming the affected
problem IDs when a change touches benchmark artifacts.

## Unreleased

- Removed the shared Model-track output-token cap. `--max-output-tokens` now
  declares a model-specific limit; omission uses provider defaults where
  supported. Anthropic requires an explicit value. Run and trajectory metadata
  record the selected limit or its omission.
- Model-track temperature is now optional and omitted from API requests by
  default. `--temperature` records an explicit model-specific value;
  `--no-temperature` remains a compatibility alias for omission.
- Evaluation now compares integer and boolean outputs exactly, with recursive
  type-aware checks for structured outputs. Numerical tolerance applies only
  to floating-point reference values; nonfinite outputs are rejected.
- The Model-track runner rejects provider-body overrides of fixed generation
  fields and records the explicit generation parameters in each trajectory.
  Provider-specific reasoning options remain configurable and disclosed.
- Fixed six LeetCode reference drivers that failed compilation (`lc7`,
  `lc2110`, `lc2960`, `lc3105`, `lc3206`, `lc413`), implemented `lc344`'s
  character-array parser, and corrected the output schema of all twelve in-place
  problems, including the two that use only an embedded harness. The harness generator now emits
  post-call argument values and any return value for in-place functions.
- Added published camelCase input-key compatibility to 32 reference drivers
  and corrected `lc1095`'s array key. Evaluation now uses benchmark drivers
  directly, without runtime repairs or inferred argument-type rewrites.
- `leetcode/lc377`: restored the O(target × n) dynamic program in `code.rs`,
  `code_spec.rs`, and `verified.rs`, replacing an exponential recursion that
  exceeded the time limit. DP entries saturate at 2^31, so intermediate counts
  cannot overflow when the answer fits in `i32`.
- `leetcode/lc643`: `code.rs`, `spec.rs`, `code_spec.rs`, and `verified.rs` now
  match the starter code. The verified `find_max_average_core` returns the
  maximum window sum as `i64`, and an unverified `find_max_average` wrapper
  divides by `k` to return `f64`, since Verus does not support floating point.
- Reference proofs now verify the supplied programs: `lc260` and `lc2956` drop
  added fallback and recomputation code, and `cf1584C` drops a string literal
  holding the original source. `leetcode/lc3233` restores the original sieve
  in `code.rs`, `code_spec.rs`, and `verified.rs`, with an integer square root
  in place of `f64::sqrt`; its `spec.rs` gains a type annotation it needed.
- 124 `verified.rs` files move proof-only snapshots and witnesses into ghost
  code and revert small refactors, so every `verified.rs` keeps the executable
  code of its `code_spec.rs`.
- `codeforces/cf1915C`, `leetcode/lc3148`: `verified.rs` adds assertions so
  the proofs no longer depend on the file name they are verified under; both
  failed as `verify.rs`, the name the scorer uses.
- `codeforces/cf1547D`: `spec.rs` and `code_spec.rs` give `is_co_growing` an
  explicit trigger, which Verus could not infer. `leetcode/lc327`:
  `code_spec.rs` defines the four spec functions its helper's postcondition
  uses.
- The ProofGen code-and-spec check (patched lynette) accepts proof-only
  termination annotations (`decreases` on executable functions, `when`/`via`
  on spec functions), `loop_isolation`, `Ghost(..)` lets, and split `impl`
  blocks. All 1,006 reference proofs pass it.
- Test drivers compile their rustc stand-ins for vstd's `set`, `get_char`, and
  `unicode_len` only without Verus; 140 reference programs failed to compile
  against them. Verus test builds use `-O`, and a driver function that the
  program also defines is dropped.
- The SpecGen typecheck stubs every executable function body; 27 reference
  specifications failed the previous stub.
- Regenerated 40 embedded test harnesses (`tests/harness.rs`) that lagged
  behind their `reference_oracle.rs` repairs or kept a generator placeholder
  (`lc680`). Removed leftover scratch files (`test.rs` in nine problems,
  `lc275/verified1.rs`, `lc523/scratch.rs`, `leetcode/README.md`) and renamed
  `lc2215/tag` to `tags`.
- Test generators: `cf1750C` and `lc7` generate inputs in the current
  specification's domain (length at least 2; any `i32`) and call the current
  functions, and `cf1750C/tests/gen.rs` emits contest stdin/stdout text; `lc2110`, `lc2960`, `lc3105`, `lc3206`, and `lc413` compile again;
  `lc1013`'s `gen_adv.rs` drops an unused stub containing `assume(false)`. All
  2,012 generators verify with `--no-cheating`. Test cases are unchanged.

## v2026.10

First tagged release. Commit `0854818`.

- 1,006 problems: 722 LeetCode, 284 Codeforces.
- Pinned to Verus `0.2026.04.10.01bf489` with
  `--no-cheating --expand-errors --rlimit 100000`; all 1,006 `verified.rs`
  files verify.
- 80 problems with multiple valid answers now have a problem-specific checker
  (`tests/checker.py`; see `benchmark/CHECKERS.md`).
- Specification fixes: 83 preconditions and 18 postconditions corrected, plus
  unsound or incomplete specifications fixed in individual problems.
- Removed `#[verifier::exec_allows_no_decreases_clause]` from all programs.

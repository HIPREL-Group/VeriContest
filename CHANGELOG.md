# Changelog

Notable changes to the VeriContest benchmark. Releases are tagged `vYYYY.MM`;
see [RELEASING.md](RELEASING.md).

Contributors: add a line under **Unreleased** in your PR, naming the affected
problem IDs when a change touches benchmark artifacts.

## Unreleased

- Moved the test cases out of the Hugging Face datasets `Gax-c/VeriContest` and
  `Gax-c/VeriContest_Lite` into one dataset of their own,
  [`Gax-c/VeriContest_Tests`](https://huggingface.co/datasets/Gax-c/VeriContest_Tests), so that the problem datasets
  stay small. The file paths are unchanged, and the tag `v2026.10.1` of
  `Gax-c/VeriContest_Tests` holds the test cases of release v2026.10.1. Earlier
  revisions of the two problem datasets still contain the test cases.
- Moved the Verus benchmark and its tooling into `benchmarks/verus/` so that
  versions for other verification tools can sit beside it. Problem folders are
  now in `benchmarks/verus/problems/` (was `benchmark/`), the bundled toolchain
  in `benchmarks/verus/toolchain/` (was `verus/`), and `evaluation/`, `lemmas/`,
  `skills/`, `test_gen/` and `post2exe/` in `benchmarks/verus/`. Commands in
  `benchmarks/verus/` run from that folder. No problem, test case, prompt or
  scoring rule changed, so entries for v2026.10.1 are unaffected.
- cf1862D: removed the test case with n = 2^63 - 1, outside the stated bound
  n <= 10^18 (one positive and its 11 negative test cases in the Hugging Face test
  cases), and removed that value from the generator's edge cases (`tests/gen.rs`).
- Added the Dafny version in `benchmarks/dafny/`: the descriptions of the 1,006
  problems with Dafny starter code, and the scorer of End2End solutions
  (`benchmarks/dafny/evaluation/`). Its reference specifications are currently
  hidden, so the maintainers score Dafny entries.
- Leaderboard: entries and evaluation settings name the verifier
  (`benchmark.verifier`, default `verus`). Entries on the Dafny version are shown
  after the Verus entries, ranked separately, with a footnote.

## v2026.10.1

Commit `0fede47`. Verus `0.2026.04.10.01bf489`.

- Added `evaluation/`: `generate.py` runs a model on a task with its fixed
  prompt, and `score.py` scores one program per problem
  (see `evaluation/README.md`).
- Fixed six LeetCode reference drivers that failed compilation (`lc7`,
  `lc2110`, `lc2960`, `lc3105`, `lc3206`, `lc413`), implemented `lc344`'s
  character-array parser, and corrected the output schema of all twelve in-place
  problems, including the two that use only an embedded harness. The harness generator now emits
  post-call argument values and any return value for in-place functions.
- Added published camelCase input-key compatibility to 32 reference drivers
  and corrected `lc1095`'s array key.
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
- `codeforces/cf1750C`, `codeforces/cf1901C`: `description.md` now gives the
  functions that `spec.rs` and `main.rs` define. `cf1750C` asks for
  `complementary_xor_ops(a, b) -> (bool, Vec<(usize, usize)>)` instead of
  `is_complementary_xor_possible(a, b) -> bool`; `cf1901C` asks for
  `min_operations(a)` and `build_operations(a)` instead of
  `build_operations(mn, mx, steps)`.
- `codeforces/cf1547D`: `spec.rs` and `code_spec.rs` give `is_co_growing` an
  explicit trigger, which Verus could not infer. `leetcode/lc327`:
  `code_spec.rs` defines the four spec functions its helper's postcondition
  uses.
- Test drivers compile their rustc stand-ins for vstd's `set`, `get_char`, and
  `unicode_len` only without Verus, so Verus programs that call these methods
  compile.
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

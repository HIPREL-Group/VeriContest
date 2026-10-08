# Changelog

Notable changes to the VeriContest benchmark. Releases are tagged `vYYYY.MM`;
see [RELEASING.md](RELEASING.md).

Contributors: add a line under **Unreleased** in your PR, naming the affected
problem IDs when a change touches benchmark artifacts.

## Unreleased

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

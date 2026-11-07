# VeriContest in Dafny

The Dafny version of VeriContest: the 1,006 problems of release v2026.10.1 (722
LeetCode, 284 Codeforces) for Dafny 4.11.0, with the same test cases as the
Verus version. A solution writes the specification, the code and the proof of a
problem in Dafny, the End2End task.

## Layout

```text
problems/
  leetcode/<pid>/description.md
  codeforces/<pid>/description.md
evaluation/        # scorer and scoring policy
```

- `problems/<family>/<pid>/description.md`: the problem statement and, under
  "Starter Code", the Dafny starter: the declarations of the two contract
  predicates `<f>_pre` and `<f>_post`, and the header of the entry method `<f>`.
  A Codeforces problem may have two entry methods, each with its own
  predicates, and its description also shows the Verus version's `main`, which
  reads the input, calls the methods and prints what they return.
- [`evaluation/`](evaluation/README.md): the scorer and its checks.

The reference specifications, Dafny translations of the Verus version's specs,
are currently hidden, so the maintainers score Dafny entries.

## Submissions

Dafny entries follow the [submission rules](../../submissions/README.md) and are
shown on the [leaderboard](https://hiprel-group.github.io/VeriContest/), ranked
separately from Verus entries.

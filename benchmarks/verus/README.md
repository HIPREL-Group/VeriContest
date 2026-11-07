# VeriContest in Verus

The Verus version of VeriContest: each problem's Rust code, Verus specification
and proof, the evaluator, the bundled Verus toolchain, and the tools that build
the benchmark. Commands in the guides under this folder run from `benchmarks/verus/`.

## Layout

```text
problems/
  codeforces/       # 284 Codeforces problems
  leetcode/         # 722 LeetCode problems
  CHECKERS.md       # Problem-specific judging rules and input/output schemas
evaluation/         # Model-track generation and the official scorer (see evaluation/README.md)
lemmas/             # Reusable Verus proof lemmas (arithmetic, bits, sequences)
skills/             # Authoring guides and scripts for adding new problems
toolchain/          # Bundled Verus toolchain, 0.2026.04.10, Linux x86-64 (invoked as ./toolchain/verus)
test_gen/           # Test case generation pipeline (positive and negative)
post2exe/           # Postcondition-testing component
```

Each problem directory contains the verification artifacts for one problem:

```text
problems/codeforces/cf1006C/
  description.md
  tags
  code.rs
  spec.rs
  code_spec.rs
  verified.rs
  main.rs
```

LeetCode problems generally expose function-style interfaces and usually do not
include `main.rs`. Codeforces problems include `main.rs` for contest-style
stdin/stdout handling.

## File Meanings

- `description.md`: Natural-language problem statement sourced from LeetCode or
  Codeforces, supplemented with starter code to support evaluation.
- `tags`: Metadata such as problem ID, difficulty level, acceptance rate, and
  algorithm tags, when available.
- `spec.rs`: The ground-truth formal specification. It contains preconditions,
  which state the properties inputs must satisfy, and postconditions, which
  specify the desired relationship between inputs and outputs.
- `code.rs`: Ground-truth Rust code accepted by the online judge. Since the
  benchmark is built to align with Verus, `code.rs` is not always directly
  compilable if submitted as-is to the LeetCode platform:
  1. Some syntax that Verus accepts is not plain-Rust compatible (for example
     certain string operations, and `.set()` on arrays/vectors in place of index
     assignment).
  2. Some LeetCode problems reference self-defined data structures that cannot
     be reused directly from the reference; these are re-declared in the
     benchmark files for completeness.
- `code_spec.rs`: The code and specification artifact used for proof-generation
  task.
- `verified.rs`: Programs with specifications, code, and Verus-checked proofs.
  Verification establishes the checked functions' contracts. 
- `main.rs`: Codeforces-only executable entry point and stdin/stdout plumbing.
- `tests/checker.py`: Problem-specific output judge, when supplied. Use it to
  accept any valid answer, not only the stored reference answer.

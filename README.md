# VeriContest

VeriContest is a competitive-programming benchmark for verifiable code
generation in Rust with Verus. It accompanies the paper **"VeriContest: A
Competitive-Programming Benchmark for Verifiable Code Generation"**
([arXiv:2605.08553](https://arxiv.org/abs/2605.08553)).

Project website:
[hiprel-group.github.io/VeriContest](https://hiprel-group.github.io/VeriContest/).

The current benchmark contains 1,006 problems: 722 from LeetCode and 284
from Codeforces. Each problem pairs a natural-language description with
expert-validated formal specifications, judge-accepted Rust code, and
Verus-checked proofs. All problems are organized by source platform. Some
problems accept multiple feasible answers and require a problem-specific
checker instead of comparison with a single expected output.

The complete dataset release, including positive and mutated negative testcase files, is
available on Hugging Face:
[Gax-c/VeriContest](https://huggingface.co/datasets/Gax-c/VeriContest).

## Repository Layout

```text
benchmark/
  codeforces/       # 284 Codeforces problems
  leetcode/         # 722 LeetCode problems
  CHECKERS.md       # Problem-specific judging rules and input/output schemas
lemmas/             # Reusable Verus proof lemmas (arithmetic, bits, sequences)
skills/             # Authoring guides and scripts for adding new problems
verus/              # Bundled Verus toolchain, 0.2026.04.10, Linux x86-64 (invoked as ./verus/verus)
test_gen/           # Test case generation pipeline (positive and negative)
post2exe/           # Postcondition-testing component
```

Each problem directory contains the verification artifacts for one problem:

```text
benchmark/codeforces/cf1006C/
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
- `verified.rs`: The full Verus-vefified programs with specifications, code, and 
  proofs. It establishes that the code satisfies the specification.
- `main.rs`: Codeforces-only executable entry point and stdin/stdout plumbing.
- `tests/checker.py`: Problem-specific output judge, when supplied. Use it to
  accept any valid answer, not only the stored reference answer.

## Benchmark

All problems are under:

- `benchmark/codeforces/`
- `benchmark/leetcode/`

The paper's primary evaluation used 946 problems (690 LeetCode and 256
Codeforces). The current unified collection contains 1,006 problems; its full
set is not the same evaluation scope as the paper. Pin the repository revision
and explicit problem list when reporting results.

VeriContest supports isolated and compositional evaluation of:

- **SpecGen**: generate formal specifications from natural-language problem
  descriptions.
- **CodeGen**: generate executable Rust code from natural language,
  specifications, or both.
- **ProofGen**: generate Verus proofs with the specification and executable code
  fixed.
- **End2End**: generate the full verified Verus program, including
  specification, executable code, and proofs.

The generated testcase files, `testcases.jsonl` and
`mutated_testcases.jsonl`, are too large to include directly in this GitHub
repository. The GitHub repository is intended to make the problem artifacts,
specifications, code, proofs, and tooling easy to inspect and version. The
complete release is available on Hugging Face:
[Gax-c/VeriContest](https://huggingface.co/datasets/Gax-c/VeriContest).

## Benchmark Construction

VeriContest is constructed through a three-phase pipeline:

1. **Manually verified seed problems**: 91 verified seed problems are manually
   built with sound and complete specifications, Rust code, and Verus proofs.
2. **Semi-automated expansion**: the benchmark is expanded to 946 problems
   through semi-automated generation with human-in-the-loop review.
3. **Testcase generation and validation**: positive and negative test cases are
   generated from the verified programs to further validate postcondition
   completeness and evaluate model-generated code and specifications.

This enchmark enforces quality along five dimensions, with each benchmark
instance reviewed by at least two human experts:

- **Code correctness and efficiency**: all code is submitted to the online judge
  to ensure that it is accepted within the time and memory limits.
- **Specification soundness**: every problem includes a Verus proof certifying
  that the judge-accepted code satisfies the specification.
- **Specification completeness**: postconditions are checked through both manual
  review and automated checking with negative test cases.
- **Specification review**: each specification is manually reviewed to avoid
  unnecessary implementation-specific constraints.
- **High-quality test cases**: the dataset includes comprehensive positive and
  negative test cases for evaluating code correctness and specification
  completeness.

## Test Case Generation

`test_gen/` holds the pipeline that produces the test suites described above,
covering Phase 3 of the construction pipeline.

Positive cases (`testcases.jsonl`) come from two Verus-verified input generators
per problem, one random and one adversarial. Each generator carries the problem's
precondition as its own postcondition and must pass Verus verification, so every
generated input is proven to satisfy the precondition rather than sampled and
filtered. Expected outputs are computed with the judge-accepted code.

Negative cases (`mutated_testcases.jsonl`) pair each of those same inputs with a
wrong output, so preconditions still hold. They are produced in three stages:
semantic mutation (LLM-written buggy variants of the reference solution),
syntactic mutation (cargo-mutants AST edits), and direct perturbation of the
reference output.

## Post2Exe

Post2Exe is the postcondition-testing component used by VeriContest. It
translates supported Verus postconditions into executable Rust programs and runs
them on negative test cases. A postcondition that accepts an incorrect output is
incomplete and must be revised.

The paper uses Post2Exe as an additional quality-assurance layer for validating
postcondition completeness. Unsupported cases, such as postconditions with
unbounded quantifiers, are reviewed manually.

Post2Exe depends on the external open-source parser
[`secure-foundations/tree-sitter-verus`](https://github.com/secure-foundations/tree-sitter-verus).
We do not vendor that repository here. See
[post2exe/EXTERNAL_DEPS.md](post2exe/EXTERNAL_DEPS.md) for the expected local
checkout path and the commit used during development.

## License

This repository contains both software tooling and benchmark data. A practical
licensing split is:

- **Apache-2.0** for repository code and tooling, including Post2Exe.
- **CC-BY-4.0** for VeriContest-authored benchmark artifacts such as
  specifications, proofs, generated tests, metadata, and dataset organization.

Problem statements are derived from LeetCode and Codeforces and remain subject
to their respective source terms.

See [LICENSE](LICENSE) for the Apache-2.0 software license and
[DATA_LICENSE.md](DATA_LICENSE.md) for the CC-BY-4.0 benchmark data license and
source-content caveats.

## Paper

VeriContest is described in:

**VeriContest: A Competitive-Programming Benchmark for Verifiable Code
Generation**

The paper introduces the benchmark construction pipeline, quality-assurance
checks, evaluation tasks, and empirical results for state-of-the-art language
models on verifiable code generation.

## Citation

```bibtex
@article{xie2026vericontest,
  title={VeriContest: A Competitive-Programming Benchmark for Verifiable Code Generation},
  author={Xie, Zichen and Pawagi, Mrigank and Liu, Yuxin and Rai, Aaditi and Shao, Lize and Berberian Jr, John and Che, Sicong and Wang, Wenxi},
  journal={arXiv preprint arXiv:2605.08553},
  year={2026}
}
```

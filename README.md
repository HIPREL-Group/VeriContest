<h1 align="center">
  <img src="docs/static/logos/vericontest-logo.png" alt="VeriContest logo" width="72" align="absmiddle">
  VeriContest
</h1>

<p align="center">
  <b>A Competitive-Programming Benchmark for Verifiable Code Generation</b><br>
  Accepted at NeurIPS 2026, Evaluations &amp; Datasets Track
</p>

<p align="center">
  <a href="https://arxiv.org/abs/2605.08553">Paper</a> ·
  <a href="https://hiprel-group.github.io/VeriContest/">Website &amp; Leaderboard</a> ·
  <a href="https://huggingface.co/collections/Gax-c/vericontest">Dataset</a>
</p>

VeriContest is a competitive-programming benchmark for verifiable code
generation in Rust with Verus. It accompanies the paper **"VeriContest: A
Competitive-Programming Benchmark for Verifiable Code Generation"**
([arXiv:2605.08553](https://arxiv.org/abs/2605.08553)), accepted at NeurIPS 2026
in the Evaluations & Datasets Track.

The benchmark contains 1,006 problems: 722 from LeetCode and 284
from Codeforces. Each problem pairs a natural-language description with
expert-validated formal specifications, judge-accepted Rust code, and
Verus-checked proofs. All problems are organized by source platform. Some
problems accept multiple feasible answers and require a problem-specific
checker instead of comparison with a single expected output.

[VeriContest Lite](leaderboard/LITE.md) is a fixed 300-problem subset for smaller
evaluations, with the full benchmark's mix of sources, difficulty levels and proof
sizes. It has its own leaderboard view, and the paper describes it in Appendix D.

The datasets are on Hugging Face:
[Gax-c/VeriContest](https://huggingface.co/datasets/Gax-c/VeriContest) and
[Gax-c/VeriContest_Lite](https://huggingface.co/datasets/Gax-c/VeriContest_Lite) hold
the problems, and [Gax-c/VeriContest_Tests](https://huggingface.co/datasets/Gax-c/VeriContest_Tests) holds the
positive and mutated negative test cases of both (about 49 GiB).

## Submitting Results

Submission intake is open for Model and Agent tracks on **releases v2026.10 and
later**; each submission names the release it used. An entry covers the full
benchmark, its LeetCode or Codeforces problems, or [VeriContest
Lite](leaderboard/LITE.md) (v2026.10.1 and later). Lite has its own leaderboard:
Lite entries are ranked there, and every full-benchmark entry also appears there,
scored on the 300 Lite problems. See
[submissions/README.md](submissions/README.md) for the steps, rules, and artifact
requirements; submissions are pull requests. Use `python3 leaderboard/manage.py
init --help` to create a submission record (`--split lite` for a Lite entry).

Pending submissions have no official score or rank. SpecGen and End2End
specifications that post2exe cannot test are reviewed under the
[specification review standard](leaderboard/SPEC_REVIEW.md). See
[leaderboard/README.md](leaderboard/README.md) for validation, evaluation-status
maintenance, and website publication.

## Repository Layout

The problem set, test cases and leaderboard are shared. Each verification tool
has its own version of the benchmark under `benchmarks/`, with its problem
files, its evaluator and its toolchain.

| Folder | Verifier | Tasks |
|---|---|---|
| [`benchmarks/verus/`](benchmarks/verus/README.md) | Verus (Rust) | SpecGen, CodeGen, ProofGen, End2End |
| [`benchmarks/dafny/`](benchmarks/dafny/README.md) | Dafny | End2End |

```text
benchmarks/
  verus/            # Verus version: problems, evaluation, toolchain and tools
  dafny/            # Dafny version: problem descriptions and scorer
leaderboard/        # Release manifest, problem lists, submission validation, and website build
submissions/        # Public metadata, component results, and maintainer reviews
templates/          # Submission templates
docs/               # Website and leaderboard (GitHub Pages)
```

## Benchmark

The Verus problems are under `benchmarks/verus/problems/codeforces/` and
`benchmarks/verus/problems/leetcode/`.

VeriContest supports isolated and compositional evaluation of:

- **SpecGen**: generate formal specifications from natural-language problem
  descriptions.
- **CodeGen**: generate executable Rust code from natural language,
  specifications, or both.
- **ProofGen**: generate Verus proofs with the specification and executable code
  fixed.
- **End2End**: generate the full verified Verus program, including
  specification, executable code, and proofs.

The paper evaluates ten state-of-the-art models on all 1,006 problems and on
VeriContest Lite. The strongest model, GPT-5.5, reaches 97.51% on
natural-language-to-code generation, but only 57.16% on SpecGen, 13.82% on
ProofGen, and 6.76% on End2End. These results are the baseline entries of
release v2026.10.1 on the [leaderboard](https://hiprel-group.github.io/VeriContest/).
When reporting results, name the release and the problem list you used.

The generated testcase files, `testcases.jsonl` and
`mutated_testcases.jsonl`, are too large to include directly in this GitHub
repository. The GitHub repository is intended to make the problem artifacts,
specifications, code, proofs, and tooling easy to inspect and version. The test
cases are on Hugging Face, in
[Gax-c/VeriContest_Tests](https://huggingface.co/datasets/Gax-c/VeriContest_Tests).

## Benchmark Construction

VeriContest is constructed through a three-phase pipeline:

1. **Manually verified seed problems**: 91 verified seed problems are manually
   built with sound and complete specifications, Rust code, and Verus proofs.
2. **Semi-automated expansion**: the benchmark is expanded to 1,006 problems
   through semi-automated generation with human-in-the-loop review.
3. **Testcase generation and validation**: positive and negative test cases are
   generated from the verified programs to further validate postcondition
   completeness and evaluate model-generated code and specifications.

The benchmark enforces quality along five dimensions, with each benchmark
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

`benchmarks/verus/test_gen/` holds the pipeline that produces the test suites described above,
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
[benchmarks/verus/post2exe/EXTERNAL_DEPS.md](benchmarks/verus/post2exe/EXTERNAL_DEPS.md) for the expected local
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

## Citation

```bibtex
@article{xie2026vericontest,
  title={{VeriContest}: A Competitive-Programming Benchmark for Verifiable Code Generation},
  author={Xie, Zichen and Pawagi, Mrigank and Liu, Yuxin and Rai, Aaditi and Shao, Lize and Berberian, Jr., John and Che, Sicong and Wang, Wenxi},
  journal={arXiv preprint arXiv:2605.08553},
  year={2026}
}
```

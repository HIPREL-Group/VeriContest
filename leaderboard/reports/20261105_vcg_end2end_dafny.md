# Review of Emergence-VCG (Emergence AI), Dafny version

Entry [`20261105_vcg_end2end_dafny`](../../submissions/20261105_vcg_end2end_dafny/): the Agent-track End2End entry of Emergence-VCG,
version `vcg-2026.11`, by Emergence AI, on the [Dafny version](../../benchmarks/dafny/README.md) of
VeriContest release v2026.10.1 (benchmark revision `0fede470992d79acb7b376fa87a25f78a5ce4a0b`),
full split. Dafny entries are ranked separately from Verus entries.

## Result

| View | Passed | Problems | Accuracy |
|---|---:|---:|---:|
| Full | 969 | 1,006 | 96.32% |
| LeetCode | 702 | 722 | 97.23% |
| Codeforces | 267 | 284 | 94.01% |
| Lite | 290 | 300 | 96.67% |

A problem passes when its program passes every check of the scorer and, where a check
goes to review, the specification review. Failures and missing programs stay in the
denominator.

## Evaluation

- Artifacts: the submitter's bundle, sha256
  `ea7df6f115bfda8d1c738da7862c50f60094b0b55daa032822694077d5a56d44`, shared privately. It
  holds 995 Dafny programs; the 11 problems without one count as failures.
  The maintainers scored the submitted programs; generation was not run again.
- Scorer: `benchmarks/dafny/evaluation/score.py` at [`36118d2`](https://github.com/HIPREL-Group/VeriContest/tree/36118d2a892831cb15f990b484d6ce709961e319/benchmarks/dafny/evaluation),
  setting `agent-end2end-nl-dafny-2026-10-1`. Its [README](https://github.com/HIPREL-Group/VeriContest/blob/36118d2a892831cb15f990b484d6ce709961e319/benchmarks/dafny/evaluation/README.md)
  lists the checks and when a problem goes to review.
- Test cases: [Gax-c/VeriContest](https://huggingface.co/datasets/Gax-c/VeriContest) at revision `55a87f82f3d8edfb7b802c6fdb9bba389f9cc571`
- Dafny `4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2`, rustc `1.95.0`
- Limits: Test case: 1 s (LeetCode: one call of the compiled method; Codeforces: one run of the program, wall clock); dafny audit: 300 s; dafny verify: 600 s with --enforce-determinism --verification-time-limit 0; dafny build and cargo build --release: 600 s each; code tests: 3600 s per problem; spec tests: 1800 s per problem; precondition proof: 60 s per lemma, 300 s per dafny verify run
- Problems whose code tests failed only by the 1 s per-case limit, or whose verification failed
  only under load, were scored again at low load.

## Review

The automatic checks passed 802 problems and failed 24. The other
180 went to human review under the [specification review standard](../SPEC_REVIEW.md):

- 146 preconditions that Dafny did not prove equivalent to the reference
  precondition: 134 passed and 12 failed. Each failure has an input, within the
  parameter types' ranges, that one precondition admits and the other rejects.
- 34 specifications that the spec tests could not decide: 33 passed and
  1 failed.

Each record of the entry's `results.jsonl` gives the problem's checks, the stage that
decided its verdict and the reason, with the witness input of a failed review;
`review.json` holds the verdicts.

## Failures

| Reason | Problems |
|---|---:|
| Precondition not equivalent to the reference (review) | 12 |
| No program | 11 |
| Code tests: test cases over the 1 s limit | 11 |
| Spec tests fail | 2 |
| Specification fails the review | 1 |
| Total | 37 |

## Limitations

- The reference specifications of the Dafny version are currently hidden, so only the
  maintainers can run the scorer.
- Code-test times were measured on the maintainers' machine.
- The specification review is a human judgment under the standard above; the automatic
  checks alone do not establish that a specification is correct.

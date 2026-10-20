# VeriContest v2026.10.1 Model-track baselines

Model-track baseline results for [VeriContest](https://github.com/HIPREL-Group/VeriContest) release
v2026.10.1 (benchmark revision `0fede470992d79acb7b376fa87a25f78a5ce4a0b`): ten models on all
six task and input-mode pairs, on the full 1,006-problem split.

## pass@1 (%)

| Model | SpecGen (nl) | CodeGen (nl) | CodeGen (spec) | CodeGen (nl_spec) | ProofGen (code_spec) | End2End (nl) |
|---|---|---|---|---|---|---|
| Claude Opus 4.7 | 27.2 | 95.4 | 77.2 | 80.6 | 12.5 | 3.6 |
| Claude Sonnet 4.6 | 17.3 | 93.8 | 82.0 | 83.8 | 13.5 | 3.5 |
| GPT-5.5 | 57.2 | 97.5 | 77.4 | 84.5 | 13.8 | 6.8 |
| GPT-5.4 mini | 7.9 | 83.9 | 54.6 | 63.0 | 6.4 | 1.5 |
| Gemini 3.1 Pro | 22.6 | 94.1 | 80.6 | 89.9 | 12.9 | 3.7 |
| Gemini 3 Flash | 22.7 | 53.1 | 32.5 | 36.6 | 6.2 | 1.3 |
| DeepSeek V4 Pro | 12.1 | 92.0 | 66.8 | 73.1 | 5.5 | 1.3 |
| DeepSeek V4 Flash | 9.7 | 82.2 | 64.3 | 64.5 | 6.4 | 1.2 |
| GLM-4.7-Flash | 3.7 | 43.3 | 17.1 | 22.2 | 5.3 | 0.7 |
| Qwen3.6-27B | 0.4 | 82.5 | 43.9 | 51.6 | 4.6 | 0.2 |

A problem passes when its program passes every automatic check of the task
(tests, Verus verification, and the specification test) and, for SpecGen and
End2End specifications that post2exe cannot test, the
[specification review](../SPEC_REVIEW.md). Failures and missing outputs stay in the
denominator.

## Evaluation

- Scorer: `evaluation/score.py` at [`ac7418f`](https://github.com/HIPREL-Group/VeriContest/tree/ac7418f95dda0ad47b800ab872c60ace5ad1c907/evaluation)
- Test cases: [Gax-c/VeriContest](https://huggingface.co/datasets/Gax-c/VeriContest) at revision `9d6cb8e6233790a0af59774e3c87b486f7e683db`
- Verus `0.2026.04.10.01bf489`, rustc `1.94.0`
- Limits: Test case: 1 s wall clock; compilation: 120 s; verification: 600 s with --no-cheating --rlimit 100000; SpecGen typecheck: 120 s; lynette compare: 30 s; post2exe: 120 s generation, 300 s checker compilation, 600 s checker run
- Test failures caused only by the 1 s per-case limit were scored again at low load.

## Files

Each leaderboard entry in `submissions/` has an archive, `<entry-id>.zip`,
containing `README.md`, `results.jsonl` (one record per problem),
`artifacts/<family>/<problem>.rs` (the scored program),
`logs/<family>/<problem>.json` (the scorer's log), and
`traces/<family>/<problem>.json` (the exact prompt, the request settings and the raw model
response). The archives' sha256 checksums are pinned in each entry's
`metadata.yaml`; the VeriContest team provides them on request.

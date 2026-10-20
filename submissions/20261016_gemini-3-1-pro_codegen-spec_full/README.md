# Gemini 3.1 Pro: CodeGen (spec)

## System

Gemini 3.1 Pro (`gemini-3.1-pro-preview`) answers each problem once from the CodeGen prompt
template `spec2code.md`, with no tools, feedback, or human intervention.

## Generation

Each prompt is the task template filled with the problem's `spec.rs`.
One request per problem; the response is the final answer. Settings: `gemini-3.1-pro-preview`: api Gemini API, temperature 0, max_output_tokens 16384.
The program is taken from the response's fenced code block as described in `evaluation/README.md`
(extraction rule `last`).

## Evaluation

Scored with `evaluation/score.py` at evaluator revision `ac7418f95dda0ad47b800ab872c60ace5ad1c907` on the full
1,006-problem split of release v2026.10.1, with the test cases of
[Gax-c/VeriContest](https://huggingface.co/datasets/Gax-c/VeriContest) at revision `9d6cb8e6233790a0af59774e3c87b486f7e683db`.
Limits: Test case: 1 s wall clock; compilation: 120 s; verification: 600 s with --no-cheating --rlimit 100000; SpecGen typecheck: 120 s; lynette compare: 30 s; post2exe: 120 s generation, 300 s checker compilation, 600 s checker run. Problems with `tests/checker.py` are judged by the checker.
Test failures caused only by the 1 s per-case limit were scored again at low load.


## Artifacts and fresh runs

The bundle `20261016_gemini-3-1-pro_codegen-spec_full.zip` contains `README.md`, `results.jsonl`,
`artifacts/<family>/<problem>.rs` (the scored program), `logs/<family>/<problem>.json`
(the scorer's log) and `traces/<family>/<problem>.json` (the exact prompt, the request settings and the raw
response). Paths in `results.jsonl` start at the bundle root. Its sha256 is pinned in
`metadata.yaml`; the VeriContest team provides it on request. The trajectories are also
published as [`2026-10.1/20261016_gemini-3-1-pro_codegen-spec_full.jsonl.gz`](https://github.com/HIPREL-Group/VeriContest-trajectories/blob/0a19f73b22fe461fc2f68a3c355930c38dba9e80/2026-10.1/20261016_gemini-3-1-pro_codegen-spec_full.jsonl.gz)
in [HIPREL-Group/VeriContest-trajectories](https://github.com/HIPREL-Group/VeriContest-trajectories), one JSON record per problem.

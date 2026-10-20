# VeriContest Lite

VeriContest Lite is a fixed 300-problem subset of the benchmark for smaller
evaluations. It keeps the full benchmark's mix of sources, difficulty levels and
proof sizes. Lite is a leaderboard split of its own: Lite entries are ranked on
Lite, and every full-split entry is also scored on the Lite problems.

| File | Contents |
|---|---|
| `lite_problem_ids.txt` | The 300 Lite problems (215 LeetCode, 85 Codeforces) |
| `lite_measurements.jsonl` | Reference-solution timings used by rule 4 |
| `make_lite.py` | The selection |

`release.json` pins `lite_problem_ids.txt` by its sha256, so the list is part of
the release and does not change within it.

## Selection criteria

The pool is every problem of the release (1,006 in 2026-10.1). A problem is
left out when:

1. its description has an image or a hyperlink;
2. its description refers to another problem;
3. its outputs are judged by a checker (`tests/checker.py`, several valid
   answers) rather than by exact comparison;
4. its reference solution uses more than half of the 1 s per-case time limit on
   some test case.

No rule looks at the proof. These rules leave 914 of the 1,006 problems.

Lite then samples 300 problems with the fixed seed `VeriContest Lite 2026-10.1`:

- **Source and difficulty.** Each source and each difficulty level keeps its
  share of the full benchmark (not of the eligible problems). LeetCode: 107 Easy,
  90 Medium, 18 Hard. Codeforces by rating: 35 at 800, 12 at 900–1000, 15 at
  1100–1200, 12 at 1300–1400, 11 at 1500 and above.
- **Proof size.** Within each group, problems are ranked by the size of their
  reference proof (the non-blank lines `verified.rs` adds to `code_spec.rs`) and
  cut into one interval per place. One problem is drawn at random from each
  interval. When the drawn problem is left out by a rule, the eligible problem of
  the same group closest to it in proof size takes its place. Lite therefore
  follows the full benchmark's proof sizes even where the rules remove problems.

Choosing problems never uses model results.

## How Lite compares with the full benchmark

Proof size, in lines:

| | Median | 75th percentile | 90th percentile |
|---|---|---|---|
| Full, LeetCode | 77 | 180 | 326 |
| Lite, LeetCode | 76 | 178 | 312 |
| Full, Codeforces | 110 | 229 | 351 |
| Lite, Codeforces | 108 | 218 | 351 |

30 Lite problems are among the 10% of benchmark problems with the largest
proofs. On the ten Model-track baselines, Lite scores are within 3 points of the
full-benchmark scores for every model and task. Kendall's τ between the Lite and
full rankings is 0.96 for SpecGen, 0.91 for CodeGen from a specification, with or
without a description, 0.80 for End2End, 0.78 for CodeGen from a description and
0.69 for ProofGen. All but one of the order changes are between models within
2.1 points of each other on the full benchmark; the exception is Claude Opus 4.7
and GPT-5.5 on CodeGen from a description and specification (80.6 and 84.5).

## Running Lite

The Lite problems and their test cases are also published on their own, as the
[VeriContest_Lite](https://huggingface.co/datasets/Gax-c/VeriContest_Lite) dataset
(about 17 GiB, against 49 GiB for the full benchmark). Pass its folder as `--testcases`.

```bash
python3 evaluation/generate.py --split lite ...
python3 evaluation/score.py --split lite ...
python3 leaderboard/manage.py init --split lite ...
```

To reproduce the selection:

```bash
python3 leaderboard/make_lite.py select     # uses lite_measurements.jsonl
python3 leaderboard/make_lite.py measure --testcases <testcases>   # re-times the references
```

Timings depend on the machine. The recorded measurements were taken with 24
problems running in parallel; every case above a quarter of the limit was timed
again on its own, as the median of three runs.

## Later releases

Lite stays comparable across releases. When a release changes or removes a Lite
problem, the replacement comes from the same group, chosen by the same rules;
the other Lite problems stay. Problems added by a release do not enter Lite
until Lite is redrawn.

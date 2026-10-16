# VeriContest Evaluation

- `generate.py` runs a model on one task: one sample per problem from the task's fixed prompt, with no tools or feedback.
- `score.py` scores one final program per problem and writes per-problem result records.

## Setup

Linux x86-64 with the bundled `verus/`, Rust 1.94.0 (`rustup toolchain install 1.94.0`), and Python 3.9+.

```bash
evaluation/setup_tools.sh                       # builds the patched lynette (needed for ProofGen)
pip install -r evaluation/requirements.txt      # only for generate.py
pip install "tree-sitter>=0.22" -e post2exe/tree-sitter-verus  # SpecGen and End2End spec tests; see post2exe/EXTERNAL_DEPS.md
```

Download the test cases from [Hugging Face](https://huggingface.co/datasets/Gax-c/VeriContest) and pass the folder as `--testcases`. It must contain `<family>/<problem>/tests/testcases.jsonl`, and `mutated_testcases.jsonl` for SpecGen and End2End.

## Generating with a model

```bash
python3 evaluation/generate.py --task End2End --input-mode nl \
  --backend anthropic --model <model-id> \
  --max-output-tokens <model-supported-limit> --out runs/my-model
python3 evaluation/score.py --task End2End --input-mode nl \
  --outputs runs/my-model/programs --testcases <testcases> --out runs/my-model/eval
```

The `--backend` values are `openai-chat` (any OpenAI-compatible server, including vLLM; set `--base-url`), `openai-responses`, and `anthropic`.

- `--max-output-tokens` and `--temperature` set the output-token limit and the temperature. Without them, the request leaves these fields to the provider, and `run.json` records `null`. `anthropic` requires `--max-output-tokens`. `--no-temperature` is an alias for leaving the temperature out.
- `--extra-body` takes a JSON object of provider settings, such as
  `{"reasoning_effort":"high"}`, `{"reasoning":{"effort":"high"}}`,
  `{"thinking":{"type":"enabled","budget_tokens":2048}}`, or
  `{"chat_template_kwargs":{"enable_thinking":true}}`. Seeds can be recorded here too.
- `--extra-body` cannot set the prompt, the model, token limits, the sample
  count, other sampling controls, stop sequences, tools, conversation state, or
  streaming, including in nested fields. Such a setting is an error, reported
  before any API call.
- `run.json` records the run's settings. Each problem gets a trajectory with
  the exact prompt, the raw response, and `request.generation_parameters`,
  built by the same function that builds the API request. A run directory holds
  one configuration; use a new output directory to change settings.

## Scoring other outputs

Write one final program per problem to `<outputs>/<family>/<problem>.rs` and run `score.py` on that folder.

## What the scorer checks

| Task | Input mode | Prompt | Checks |
|---|---|---|---|
| SpecGen | `nl` | `nl2spec.md` | Executable bodies stubbed, then `verus --no-verify` (parse and typecheck); then the [specification test](#specification-tests) |
| CodeGen | `nl` | `nl2code.md` | Compile with `rustc -O` in the problem harness, then run every positive test case |
| CodeGen | `spec`, `nl_spec` | `spec2code.md`, `nl_spec2code.md` | Same tests; Verus programs compile with `verus --no-verify --compile -O`, other programs are stripped and compiled with `rustc -O` |
| ProofGen | `code_spec` | `spec_code2proof.md` | `lynette compare -t` against `code_spec.rs` (see [ProofGen code-and-spec check](#proofgen-code-and-spec-check)), then `verus --no-cheating --rlimit 100000` |
| End2End | `nl` | `end2end.md` | Verus as above; if it verifies, the test cases; if they pass, the [specification test](#specification-tests) |

Each test case has a 1 s wall-clock limit. Verification has 600 s and compilation 120 s. A problem passes when every automatic check passes. For SpecGen and End2End, a problem whose specification post2exe cannot test needs human specification review instead.

**Test harness.** Programs run in the problem's own test driver and receive
only the test input on stdin. LeetCode problems use `tests/reference_oracle.rs`
(or the embedded `tests/harness.rs`); Codeforces problems use `main.rs`, with
the program's `impl Solution` in place of its own. Where the program defines a
function or constant that `main.rs` also defines, the program's definition is used.

**Output comparison.** Problems with `tests/checker.py` are judged by the
checker (`benchmark/CHECKERS.md`). Otherwise, JSON integers and booleans must
match exactly in value and type; strings match with surrounding whitespace
ignored; arrays and objects are compared element by element, including their
lengths and keys. A floating-point reference value accepts a finite number
within `1e-6 * max(1, |expected|)`. A Codeforces program's standard output is
compared with the expected output as a string.

**SpecGen typecheck.** Every executable function body, in any `impl` and with any return type, is replaced by `loop {}`, which typechecks as any type.

**Extraction.** SpecGen, CodeGen `nl`, and ProofGen take the first fenced code block of a response. The other modes take the last block that contains `impl Solution` or `verus!`. A response without a fenced block is used whole.

**Output.** The scorer writes `results.jsonl` (one record per problem), one log per problem in `eval_logs/`, and `summary.json` (counts, the automatic pass@1, and the toolchain and evaluator revision).

## Specification tests

`spec_tests` (SpecGen and End2End) runs [post2exe](../post2exe/README.md) on the
answer's specification. post2exe lowers the specified function's precondition
and postcondition into an executable checker, which is run on the problem's
test cases:

- **pass:** it accepts every positive case (input with the reference output),
  rejects every negative case (`mutated_testcases.jsonl`: same input, wrong
  output), and its precondition admits every input the reference
  specification admits.
- **fail:** it rejects a correct output, accepts a wrong one, or its
  precondition excludes valid inputs.
- **unsupported:** human review, with the reason recorded (`review_reason` in
  the log and the result's notes, `spec_review_problem_ids` in
  `summary.json`): `timeout` (limits in `vceval/config.py`) or `post2exe cannot
  handle it`. post2exe's own message is kept in the log.

The problem's reference `spec.rs` is run the same way first. If post2exe cannot
test it cleanly (or it disagrees with its own test cases), the problem goes to
human review with the same reasons.

## ProofGen code-and-spec check

`setup_tools.sh` builds lynette ([microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis) at `af0d0f4`) with `patches/lynette.patch`. `lynette compare -t` checks that an answer keeps the executable code and the specification of `code_spec.rs`:

- Spec functions from `code_spec.rs` must stay the same (proof statements inside them, and the `when`/`via` termination parts of their `decreases`, excepted).
- Only ghost code is removed before the comparison; executable structure is kept. `let x = Ghost(..)` / `Tracked(..)` counts as ghost code.
- New spec functions are allowed, and so are `ensures` and `decreases` on an executable function that had none, and `requires` on a function another function of the original calls (a recursive call to itself does not count). Lint, doc, and verifier attributes, `#[verifier::loop_isolation(..)]` on a loop, `use vstd::..`, `broadcast` items, an empty `else`, and splitting an inherent `impl` into adjacent blocks are ignored.
- Items outside `verus!`, and in a `verus!` nested in a `mod`, are checked too.

Two Verus forms that lynette's parser does not read, the `returns` clause and an `ensures` block expression, are rewritten the same way on both sides before the comparison (`checks.lynette_compatible`).

Every reference proof (`verified.rs` against `code_spec.rs`) passes the check, and answers that redefine or delete a spec function from `code_spec.rs` are rejected.

## Tests

```bash
python3 -m unittest discover -s evaluation/tests
```

SDK request tests use local mock HTTP transports and make no API calls. They
require the SDK dependencies above; the remaining tests use the standard library.

# VeriContest Test Case Generator

| File | Role | Property under test |
|---|---|---|
| `tests/testcases.jsonl` | **positive** cases | the postcondition must **accept** every case |
| `tests/mutated_testcases.jsonl` | **negative** cases | the postcondition must **reject** every case |

Both live under `benchmark/<kind>/<problem>/tests/`, where `<kind>` is `leetcode` or
`codeforces`. Each line is a JSON object `{"input": ..., "output": ...}`.

A positive case pairs a precondition-satisfying input with the reference answer.
A negative case pairs that **same input** with a **wrong** answer. Inputs are never
perturbed, only outputs, so every negative case still satisfies the precondition.

Every artifact generated for a problem (the two `.jsonl` suites plus `gen.rs`,
`gen_adv.rs`, `harness.rs` and `reference_oracle.rs`) is written into that
problem's own `tests/` folder, which `build_harness.py` creates and the later
stages fill in.

## Layout

```
test_gen/
├── gen_testcases.py            positive pipeline driver (batch LLM + validate)
├── build_harness.py            emits/compiles tests/harness.rs per problem
├── run_generators.py           compiles + runs the Verus generators
├── cf_batch4_stdio.py          CF main.rs verifier (invoked by run_generators.py)
├── verus_deps/                 support crate: vendors serde/serde_json for Verus
├── mutate_test_leetcode/       negative pipeline (LeetCode)
│   ├── llm_batch.py            stage 1: request buggy variants
│   ├── run_variants.py         stage 1: run them, keep disagreeing outputs
│   ├── syntactic_mutator.py    stage 2: cargo-mutants AST edits
│   ├── symbolic_mutator.py     stage 3: type-directed output perturbation
│   ├── mutate.py               combines all three into mutated_testcases.jsonl
│   ├── harness_utils.py        compile/run/splice helpers
│   └── cache/<pid>/            per-problem intermediates (see below)
└── mutate_test_codeforces/     same pipeline, cf_-prefixed (string stdin/stdout)
```

The `cache/<pid>/` directories hold pipeline intermediates and are **inputs to
later stages**, not scratch space. Do not delete them without regenerating:

```
variant_{1..5}.rs         buggy variants extracted from the LLM response
raw_response.txt          unparsed model output (provenance)
incorrect_llm.jsonl       stage 1 output: semantic-mutant wrong answers
incorrect_syntactic.jsonl stage 2 output: cargo-mutants wrong answers
run.log / syntactic.log   per-variant retain/drop decisions
```

## Requirements

- Python 3.9+
- `rustc` (edition 2021) and `cargo` on `PATH`
- [`cargo-mutants`](https://github.com/sourcefrog/cargo-mutants) for the syntactic stage
- Verus at `<repo>/verus/verus` for the generator verification step
- `OPENAI_API_KEY` for the semantic mutation

Both LLM stages (`gen_testcases.py` and `llm_batch.py`/`cf_llm_batch.py`) go
through the OpenAI Batch API by default, which is why each has
a `prepare`/`submit`/`poll` split and completes asynchronously within a 24h window
rather than returning immediately.

`run_generators.py` runs `cargo build` in `verus_deps/` on first use, which needs
network access to fetch serde and serde_json from crates.io. That crate is never
imported; it exists only so Verus, which has no package manager, can link the
resulting rlibs via `--extern` when compiling each `tests/gen.rs`. Its
`rust-toolchain.toml` pin must match Verus's bundled rustc
(`verus/verus --version`), otherwise the rlibs will not link.

## Positive pipeline

Two Verus-verified generators per problem, roughly 100 cases each, deduped to a
final suite of roughly 150 to 200 cases.

1. **Random** (`tests/gen.rs`): broad coverage of the valid input space.
2. **Adversarial** (`tests/gen_adv.rs`): the model analyses the problem itself and
   picks its own generator CLI arguments targeting failure modes specific to that
   problem, then supplies roughly 20 commands over a range of sizes.

The load-bearing constraint is that **each generator carries the problem's
precondition as its own postcondition and must pass Verus verification**. Inputs
are therefore proven to satisfy `requires`, not sampled and filtered. Expected
outputs come from the ground-truth solution via `tests/harness.rs`, followed by a
postcondition check and dedup on `(input, output)`.

```bash
cd <repo root>

# 1. one-time: build + compile the per-problem harnesses
python3 test_gen/build_harness.py --all --compile

# 2. batch-generate the generators
python3 test_gen/gen_testcases.py prepare --kind leetcode
export OPENAI_API_KEY=sk-...
python3 test_gen/gen_testcases.py submit
python3 test_gen/gen_testcases.py poll  

# 3. verify generators, run them, compute + check expected outputs
python3 test_gen/gen_testcases.py validate --timeout 30

# 4. inspect / retry
python3 test_gen/gen_testcases.py status -v
python3 test_gen/gen_testcases.py retry
```

## Negative pipeline

Three stages with a staged budget. Code mutants (stages 1 and 2) are collected
first up to **8x** the positive-set size; direct output mutation then fills the
remainder to the **10x** target. The split keeps the negative set anchored on
outputs that a plausible buggy implementation actually produced, and uses blind
perturbation only for the rest.

```
code_target = 8  x |positives|      --code-multiplier
target      = 10 x |positives|      --multiplier

stage 1  semantic   -> capped at code_target
stage 2  syntactic  -> tops up to code_target
stage 3  direct     -> fills to target
```

### Stage 1: semantic mutation (`llm_batch.py`, `run_variants.py`)

Prompts a model with the description and the verified solution, asking for **five**
subtly broken variants that preserve all signatures and draw on *distinct* bug
categories (off-by-one, wrong comparator, swapped indices, missing edge case,
wrong initialization, accumulator reset). Each variant is spliced into the problem
harness, compiled, and run over the positive set.

**Retention rule:** a variant counts only when its pass rate on the positive set
is *strictly* between 0% and 100%. A variant that passes everything exhibits no
observable bug; one that fails everything is trivially broken rather than subtly
buggy. Rejected variants never touch the dedup set, so they cannot suppress an
identical finding from a later variant. Every retain/drop decision is logged with
its pass rate.

Wrong answers from retained variants land in `cache/<pid>/incorrect_llm.jsonl`.

### Stage 2: syntactic mutation (`syntactic_mutator.py`)

Uses `cargo mutants --Zmutate-file --list --json` purely as a mutation
*enumerator*: operator swaps, negated conditionals, and return-value replacements
over `code.rs`. No cargo workspace is needed. Each descriptor carries a source
span and a replacement, so the edit is applied directly and the result reuses the
same harness compile/run path as stage 1.

The same retention rule applies, results are deduped against stage 1, and the
stage stops once the 8x budget is met. Mutants that fail to typecheck are expected
and skipped. Output: `cache/<pid>/incorrect_syntactic.jsonl`.

### Stage 3: direct output mutation (`symbolic_mutator.py`)

Perturbs the reference output without running any code, dispatching on its runtime
type:

| Type | Perturbations |
|---|---|
| int, float | deltas `±1, ±2, ±5, ±10, ±100`, sign flip, zero, doubling, halving, bounded random offsets |
| bool | logical negation |
| string | empty, prefix/suffix insertion, head/tail truncation, reversal, single-character replacement, adjacent-character swap |
| vec of int | per-element `±1`, pairwise swap, prepend/append, reversal, ascending/descending sort, zero an element, global `±1` shift, element-wise negation |
| vec of bool/string, matrix of int | analogous, with a generic fallback (drop first/last, reverse, empty) for unrecognized element types |

Mutations are drawn **round-robin**, one per positive input per pass, so the set
stays balanced across inputs rather than exhausting a single anchor case. Dedup
covers the reference output and every mutation already retained for that input.

Codeforces outputs are arbitrary text, so `cf_symbolic_mutator.py` classifies each
as `single-int`, `yes-no`, `num-tokens`, or `generic` and preserves the trailing
newline so mutants stay plausibly well-formed.

### Running it

Stage order matters: stage 2 reads stage 1's output to compute its remaining
budget, and `mutate.py` reads both.

```bash
cd test_gen/mutate_test_leetcode

# stage 1
python3 llm_batch.py prepare
python3 llm_batch.py submit && python3 llm_batch.py poll
python3 llm_batch.py extract
python3 run_variants.py run --workers 8

# stage 2
python3 syntactic_mutator.py run --workers 8

# stage 3 + assemble
python3 mutate.py run --workers 8
```

Codeforces is identical with the `cf_` prefixes inside `mutate_test_codeforces/`.

By default `mutate.py` skips problems that already have
`mutated_testcases.jsonl`; pass `--include-with-mutated` to regenerate. The
`--seed` default of 0 makes stage 3 deterministic.

Useful knobs:

| Flag | Default | Effect |
|---|---|---|
| `--multiplier` | 10 | final negative-set size, as a multiple of positives |
| `--code-multiplier` | 8 | share reserved for stages 1 and 2 |
| `--max-mutants` | 200 | per-problem cap on cargo-mutants edits evaluated (0 = uncapped) |
| `MUTATE_NUM_VARIANTS` | 5 | buggy variants requested per problem (env var) |
| `MUTATE_MODEL` | see source | model used for semantic mutation (env var) |

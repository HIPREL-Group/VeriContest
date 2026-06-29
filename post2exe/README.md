# post2exe

`post2exe` turns a Verus postcondition into an executable Rust checker that can
be compiled and run on benchmark testcases.

The goal is practical testing, not proof replacement. A generated checker lets
you answer questions like:

- does the postcondition lower into executable code at all
- does it accept the benchmark outputs
- is it obviously too weak on concrete tests

## Current Backend Strategy

`post2exe` now has two backends:

1. **Direct Rust backend**: preferred. It translates helper `spec fn`s and the
   target postcondition into plain Rust.
2. **Macro fallback**: used only when direct lowering fails. It reuses
   [gen_test_post.py](gen_test_post.py)
   and emits an `exec_spec_unverified!`-based checker.

Generated files start with one of:

- `// post2exe-backend: direct`
- `// post2exe-backend: macro`

That first line is the quickest way to see which path a problem used.

## Requirements

Base requirements:

- Python 3.9+
- `tree_sitter`
- `tree_sitter_verus`
- the local parser shared library at
  `post2exe/tree-sitter-verus/verus.so`

`tree_sitter_verus` comes from the external
[`secure-foundations/tree-sitter-verus`](https://github.com/secure-foundations/tree-sitter-verus)
repository. VeriContest does not vendor that repository. See
[EXTERNAL_DEPS.md](EXTERNAL_DEPS.md) for the expected local checkout path and
commit.

For compilation and execution:

- `rustc` for the direct backend
- Verus at `verus/verus` in the repo root for macro-fallback cases

Python setup from the repo root:

```bash
cd /path/to/VeriContest
pip install "tree-sitter>=0.22"
pip install -e post2exe/tree-sitter-verus
```

## Quick Start

All commands below assume you are in the repo root:

```bash
cd /path/to/VeriContest
```

Generate one checker into a temp directory:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/leetcode/lc1 \
  --out-dir /tmp/post2exe_demo \
  --force
```

Compile that checker:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/leetcode/lc1 \
  --out-dir /tmp/post2exe_demo \
  --compile \
  --force
```

Run that checker on the benchmark testcases:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/leetcode/lc1 \
  --out-dir /tmp/post2exe_demo \
  --run \
  --force
```

`--run` automatically implies `--compile`.

## How To Run

Generate one problem in place:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/leetcode/lc1004
```

Generate one problem into a separate tree:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/codeforces/cf1279B \
  --out-dir /tmp/post2exe_one \
  --force
```

Generate and compile one problem:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/leetcode/lc2425 \
  --compile \
  --out-dir /tmp/post2exe_one \
  --force
```

Generate, compile, and run one problem:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/codeforces/cf1279B \
  --run \
  --out-dir /tmp/post2exe_one \
  --force
```

Generate the whole corpus:

```bash
python3 post2exe/gen_post2exe.py \
  --all \
  --out-dir /tmp/post2exe_all \
  --force
```

Generate and compile the whole corpus:

```bash
python3 post2exe/gen_post2exe.py \
  --all \
  --compile \
  --out-dir /tmp/post2exe_all_compile \
  --force
```

Restrict the corpus to one benchmark family:

```bash
python3 post2exe/gen_post2exe.py \
  --all \
  --kind leetcode \
  --compile \
  --out-dir /tmp/post2exe_lc \
  --force
```

Print the generated Rust without writing files:

```bash
python3 post2exe/gen_post2exe.py \
  --problem benchmark/leetcode/lc1 \
  --dry-run
```

## What Gets Written

For problem `benchmark/leetcode/lc1`:

- generated checker:
  `/tmp/post2exe_demo/lc1/tests/test_post.rs` when `--out-dir` is used
- in-place checker:
  `benchmark/leetcode/lc1/tests/test_post.rs` without `--out-dir`
- compiled binary:
  `/tmp/lc1_test_post`

At runtime the generated checker reads:

- `tests/testcases.jsonl` for `--soundness` (the postcondition must accept every case)
- `tests/mutated_testcases.jsonl` for `--completeness` (the postcondition must reject every case)

When the binary is run from an `--out-dir` build, missing files are looked up in
the original benchmark `tests/` directory as a fallback.

Each line is a JSON object whose top-level shape is
`{"input": {...}, "output": ...}`.  The runtime flattens `input` into the top
level before binding parameters, and the return value is read from `output`.

## Command-Line Flags

- `--problem`: generate one benchmark directory
- `--all`: process the whole corpus
- `--kind leetcode|codeforces`: restrict `--all`
- `--compile`: compile the generated checker
- `--run`: run the compiled checker after successful compilation (defaults to
  running both phases when neither `--soundness` nor `--completeness` is given)
- `--soundness`: when running, validate `testcases.jsonl` (postcondition must
  accept every case); implies `--run` and `--compile`
- `--completeness`: when running, validate `mutated_testcases.jsonl`
  (postcondition must reject every mutated case); implies `--run` and
  `--compile`. May be combined with `--soundness`
- `--out-dir`: write to a separate output tree
- `--force`: overwrite existing generated files
- `--dry-run`: print generated Rust to stdout
- `--run-timeout`: seconds to allow each compiled checker run before killing
  it (default: `600`)

The compiled checker also accepts `--soundness` / `--completeness` directly, so
you can run the binary by hand against either testcase file.

```bash
/tmp/lc1_test_post --soundness
/tmp/lc1_test_post --completeness
/tmp/lc1_test_post --soundness --completeness   # or no flag, same effect
```

## What `--compile` Actually Does

Compilation depends on the backend used for that generated file:

- **direct backend**: compiled with `rustc --edition=2021`
- **macro backend**: compiled with `verus --compile`

That means:

- for a direct-only single-problem test, `rustc` is enough
- for corpus-wide compile runs, you should assume Verus is still needed because
  some problems still fall back to the macro backend

## Supported Runtime Shapes

The generated runtime currently handles top-level and nested combinations of:

- primitive integers
- `bool`
- `char`
- `String`
- `Seq<T>`
- `Option<T>`
- `Set<T>`
- `Map<K, V>`
- tuples
- borrowed inputs by parsing owned values and borrowing at the call site

## Expected Blockers

Some problems are skipped on purpose because the postcondition is not currently
convertible into executable Rust.

Common blockers:

- unbounded quantifiers
- quantifiers over unsupported non-primitive element types such as `Seq<int>`
- `old(...)`
- unsupported receivers such as `&self`
- opaque runtime objects
- return type `Self`
- Verus-only constructs with no direct executable analogue

When a problem is skipped, the script reports the blocker instead of emitting a
known-bad checker.

## Non-Goals

This tool is not trying to be:

- a general Verus-to-Rust compiler
- a verifier
- a semantics-preserving implementation of all Verus features

It is a benchmark tool for executable postcondition testing.

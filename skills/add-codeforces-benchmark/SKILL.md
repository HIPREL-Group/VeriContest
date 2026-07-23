---
name: add-codeforces-benchmark
description: Step-by-step process for adding a new Codeforces problem to the VCG-bench benchmark suite. Use this skill when asked to add, create, or scaffold a new Codeforces benchmark problem, or when working on verified Rust (Verus) solutions for Codeforces problems. The contest ID and problem index (e.g. 1 A, 158 A) should be provided. Only problems with rating <= 1600 are in scope.
---

# Adding a New Codeforces Benchmark

Each problem lives in `benchmark/codeforces/cf<contestId><index>/` containing 7 files.

### I/O vs Algorithm Separation

Unlike LeetCode (where you implement a single function), Codeforces requires a
complete program that reads from stdin and writes to stdout. Since **Verus cannot
verify I/O**, every benchmark splits the solution into two parts:

1. **`main.rs`** — A complete, runnable Rust program. Contains a `main()`
   function that handles all I/O (parsing stdin, formatting stdout) and calls the
   algorithm function from `impl Solution`.
2. **`code.rs`** — The pure algorithm only, inside `impl Solution { ... }`. No
   I/O, no `main()`. This is the function that gets formally verified.

`spec.rs`, `code_spec.rs`, and `verified.rs` all correspond to the algorithm
function in `code.rs` — they never contain I/O code.

## Prerequisites

- Verus is bundled at `./verus/verus` (run from the VeriContest root) to validate proofs.
- Python 3 is needed to run the fetch script.

## Step 1: Choose a Suitable Problem

Pick a Codeforces problem that:
- Has a **rating of 1600 or below**. The fetch script enforces this limit and
  rejects problems with rating above 1600 or with no rating assigned. Higher-rated
  problems are typically too complex — prefer clear specs and algorithms that stay
  within Verus-supported features.
- Is **not** already present in `benchmark/codeforces/` (check existing `cf*` directories).
- Is **not** recorded in `benchmark/codeforces/failed.md` as a previously attempted but abandoned problem.
- Read `supported_rust_features.md` (bundled with this skill) for details on what is currently supported in Verus. Avoid problems that require unsupported or partially supported features, as they will be difficult or impossible to verify.
- Uses only arrays/vectors, integers, and simple control flow.
- Has properties that are **amenable to formal verification** (e.g., sortedness, uniqueness, element preservation, index relationships, mathematical invariants).
- No `BTreeMap`, `BinaryHeap`, or other collections that Verus does not support.
- No string or float manipulation.

## Step 2: Fetch the Problem Description and Tags

Run the fetch script:

```
python3 scripts/fetch_cf_problem.py <contestId> <index>
```

This writes `description.md` and `tags` into this skill's own
`result/cf<contestId><index>/` folder (i.e.
`skills/add-codeforces-benchmark/result/cf<contestId><index>/`) by querying the
Codeforces API and scraping the problem page. Move the generated files into
`benchmark/codeforces/cf<contestId><index>/` when integrating into the benchmark
suite.

Unlike LeetCode, Codeforces does **not** provide language-specific starter code.
You must design the function signature from the problem's input/output
specification (see Step 4).

**Important:** The fetch script's HTML-to-Markdown conversion may produce an ugly
output that may have to be cleaned up to produce a well-formatted `description.md`.

## Step 3: Research Efficient Solutions from Codeforces Editorials

Before writing any code, fetch the editorial and top solutions for the problem:

```
python3 scripts/fetch_cf_solutions.py <contestId> <index>
```

This script searches for the contest editorial (from the contest author's blog
entries) and lists top accepted submissions. Codeforces editorials typically
describe the intended approach and complexity.

Note: Codeforces does not expose submission source code through its public API.
To view actual solution code, visit the contest status page linked in the script
output.

Use the insights from editorials and solutions to inform the algorithm you write
in Steps 6 and 7, but always ensure the implementation conforms to the Verus
constraints described in this skill.

**Always prefer the optimal solution.** Choose the algorithm with the best
time and space complexity that is feasible to verify in Verus. Avoid brute-force
or naive approaches when an efficient algorithm exists.

## Step 4: Design the Algorithm Function Signature and Write `spec.rs`

Since Codeforces problems don't provide starter code, you must extract the core
algorithmic function from the problem description. This function is the
**executable function** that will be verified — it must be pure (no I/O).

- **Ignore I/O entirely.** The algorithm function takes already-parsed inputs as
  parameters and returns the computed answer. All stdin/stdout handling belongs in
  `main.rs`, not here.
- **Choose appropriate types.** Use `Vec<i64>`, `i32`, `u64`, etc. based on the
  constraint bounds. Prefer signed types when negative values are possible.
- **Name the function descriptively.** Use a name that reflects the problem's
  task (e.g., `min_flagstones`, `max_subarray_sum`), not generic names like
  `solve`.

`spec.rs` should include:
- The `use vstd::prelude::*;`, `fn main() {}`, `verus! { ... }` wrapper.
- `pub struct Solution;`
- Any `spec fn` helpers needed by the specification.
- The target function with the designed signature.
- `requires` clauses that encode input constraints from the problem statement.
- `ensures` clauses that encode the intended correctness result of the problem.
- An empty body `{ }`.

**Important:** The spec must align with `description.md` exactly (constraints,
return meaning, and observable post-state behavior).

**Do not mirror the implementation.** The specification should capture *what* the
correct answer is, not *how* it is computed. Derive `requires` and `ensures`
clauses directly from the problem description's constraints and expected output,
not from the algorithm you plan to write. A good spec is one that an independent
implementation could also satisfy.

## Step 5: Write `main.rs`, `code.rs`, and `code_spec.rs` from `spec.rs`

Implement the algorithm only after the spec is defined.

### `main.rs`
This is the complete, runnable Codeforces submission. It contains:
- A `main()` function that reads from stdin, parses the input, calls the
  algorithm function via `Solution::function_name(...)`, and prints the result
  to stdout.
- A `struct Solution;` declaration and `impl Solution { ... }` block with the
  same algorithm as `code.rs`.

`main.rs` is **not verified** — it exists so the solution can be submitted to
Codeforces and tested against sample inputs. It may use any standard Rust
features for I/O (e.g., `std::io`, iterators for parsing).

### `code.rs`
This contains **only the algorithm function** — no I/O, no `main()`.
- Implement the algorithm in plain Rust using the exact signature from `spec.rs`.
- Use `impl Solution { ... }` wrapper (no `pub struct Solution;`, no `use` imports).
- Use `while` loops or `for i in 0..n` — avoid iterators, closures, and `for x in vec`.
- Use `nums[i]` indexing — no `.iter()`, `.map()`, `.filter()`, etc.
- For mutation, use direct assignment (`nums[i] = val`).
- No `HashMap`, `HashSet`, `BTreeMap`, or other collections.
- No `match` on `Option`/`Result` unless using `checked_*` arithmetic.
- Avoid `as` casts where possible; use them only for `usize`↔`i32`/`i64` at
  return boundaries.

### `code_spec.rs`
- Copy the algorithm from `code.rs` into Verus form while preserving behavior.
- Keep the Verus wrapper, `pub struct Solution;`, function signature, `requires`,
  `ensures`, and any helper `spec fn` from `spec.rs`.
- Do **not** include proof blocks, ghost variables, loop invariants, or decreases.
- For vector mutation in Verus code, use `nums.set(idx, val)`.

## Step 6: Write `verified.rs`

This is the fully Verus-verified version. It must:

1. Start with `use vstd::prelude::*;`, `fn main() {}`, and `verus! { ... }` wrapper.
2. Declare `pub struct Solution;` inside the `verus!` block.
3. Include `requires` (preconditions from the problem constraints) and `ensures`
   (postconditions capturing the problem's correctness properties).
4. Include loop `invariant` clauses and `decreases` clauses.
5. Include `proof { ... }` blocks with assertions where the solver needs help.
6. Use `#[trigger]` annotations on quantifiers where Verus cannot auto-infer triggers.
7. Use `nums.set(idx, val)` instead of `nums[idx] = val` for mutable vector writes
   (Verus requires this for reasoning about old vs new state).
8. Use `ghost` variables and `old(nums)` to refer to pre-state.

**Validate by running:**
```
./verus/verus benchmark/codeforces/cf<contestId><index>/verified.rs --no-cheating --expand-errors --rlimit 100000
```
It must report `N verified, 0 errors`.

### Proof Quality

Keep proofs minimal and purposeful. Remove assertions that are redundant or trivially dischargeable:

- **No ghost-redundant assertions.** Do not assert `x as int == spec_fn(...)` immediately after `let x = val` when an earlier assertion or proof block already established the spec equivalence of `val`. The variable binding is transparent to Verus.
- **No duplicate quantifier triggers.** If a `proof { assert(seq[j] == ...) }` block already instantiates a loop-invariant quantifier at a specific index, do not repeat an equivalent `assert` after the proof block for the same index.
- **No trivial intermediate steps.** Assertions that follow in one arithmetic step from the immediately preceding assertion (e.g. `assert(a - b == c)` right after `assert(a == c + b)`) should be omitted; the solver handles single-step arithmetic.

### Shared Lemma Library

Before writing proof lemmas, check `lemmas/` (`arithmetic.rs`, `bits.rs`,
`seq_lemmas.rs`) for reusable ones. Each `verified.rs` must still be
self-contained — **do not import from `lemmas/`**. Instead, copy any needed
lemmas directly into the `verified.rs` file.

If you write a new **generic/reusable** lemma (not tied to `Solution::*` specs),
add it to the appropriate file in `lemmas/` as well, so it is available as a
reference for future benchmarks.

### Common Verus Patterns

- **Preconditions:** Encode the problem's constraints (array length bounds, element
  value bounds, integer ranges from the problem statement, etc.).
- **Postconditions:** Encode what the problem asks to prove (e.g., correct
  computation, optimal answer, all conditions satisfied).
- **Triggers:** When using `forall` with `exists` inside, annotate the outer
  quantifier's body with `#[trigger]` on a suitable term (often `old(nums)[i]` or
  `nums[j]`).
- **Decreases:** Every `while` loop needs a `decreases` clause (e.g., `n - i`).

## Step 7: Back-propagate refinements to `main.rs`, `code.rs`, and `code_spec.rs`

After `verified.rs` succeeds, align implementation files with the final verified
algorithm:

- Update `code_spec.rs` to match the verified algorithm structure (without proof, ghost vars, loop invariants, and decreases).
- Update `code.rs` to match the same final algorithm in plain Rust form.
- Update the algorithm function inside `main.rs` to match `code.rs`.
- Keep function signatures and behavior consistent across `spec.rs`, `code_spec.rs`, `code.rs`, `main.rs`, and `verified.rs`.

**Validate consistency by running:**
```
python3 scripts/check_consistency_cf.py benchmark/codeforces/cf<contestId><index>
```
It must report no inconsistencies.

### Sanity-check the spec

Screen the spec for adequacy defects:

```
python3 -m spec_testing.run_sanity cf<contestId><index>
```

It prints a per-flag report and exits `0` clean / `1` flagged / `3` unsupported. Act on what it prints:
- `vacuity` failure or `SEED_PRE_REFUTED` → real spec bug (contradictory/wrong `requires`); fix `spec.rs` and re-run.
- A static `S*` flag is heuristic: fix only if the spec truly under-specifies the problem; otherwise it may be description-faithful — note why and move on.
- `3` (unsupported spec shape) is not a bug; proceed.

### Symbolic spec test

Once sanity is clean, test the spec against generated correct/wrong outputs (uses `main.rs` as reference):

```
python3 -m spec_testing.run_symbolic cf<contestId><index>
```

It prints per-case verdicts plus any `FINDING` lines, and exits `0` clean / `1` findings / `3` unsupported. Every finding is Verus-backed (zero false positives), so act on each:
- `soundness` → spec rejects a correct output (`requires`/`ensures` too strong).
- `incompleteness` → spec accepts a wrong output (`ensures` too weak).

Fix `spec.rs`, re-align `code_spec.rs`/`verified.rs`, then re-run **with `--force`** (it skips otherwise) until clean. `3` (unsupported) is not a finding; proceed.

## Step 8: Final Cleanup and Validation

1. For `description.md`, ensure the formatting is clean and well-structured.
2. For all code files, remove all the comments.

**Some tips:**
- Codeforces problems often involve large integer ranges (up to 10^9 or 10^18).
  Be mindful of overflow — choose `i64` or `u64` when `i32` would overflow.
- For in-place mutation functions (`&mut Vec`), check the mutated vector after the call.

## File Summary

| File             | What it contains                                             |
|------------------|--------------------------------------------------------------|
| `description.md` | Problem statement in Markdown (faithful to Codeforces)       |
| `tags`           | Line 1: rating, Line 2: topics, Line 3: solved count        |
| `main.rs`        | Complete program: I/O in `main()` + algorithm (not verified) |
| `code.rs`        | Algorithm only, plain Rust (no I/O, no Verus, no proofs)     |
| `spec.rs`        | Verus requires/ensures + empty body (the verification task)  |
| `code_spec.rs`   | Verus requires/ensures + algorithm body (no proofs)          |
| `verified.rs`    | Full Verus proof (must pass `verus` verification)            |

## When to Abandon a Problem

If after repeated attempts you are unable to produce a correct spec, a working
implementation, or a verifiable proof — **drop the problem and pick a different one.** Delete the partial `cf<contestId><index>/` directory and restart from Step 1. 

Not every Codeforces problem is tractable in Verus. Common reasons to abandon:
- The specification becomes circular or mirrors the implementation instead of the
  problem description.
- The proof requires non-linear arithmetic or bit-level reasoning that Verus
  cannot discharge within a reasonable resource limit.
- The optimal algorithm needs data structures or language features unsupported by
  Verus.
- Verification repeatedly times out or produces errors that resist targeted fixes.
- The problem fundamentally relies on string manipulation, graph traversal, or
  I/O patterns that don't translate cleanly to Verus verification.

Do not spend unbounded effort on a single problem. Move on and invest time in a problem that yields a clean spec, implementation, and proof.

## Reference Examples

Study the existing Codeforces benchmarks in `benchmark/codeforces/` for Verus patterns:
- `cf110A/`
- `cf466C/` 
- `cf474B/` 

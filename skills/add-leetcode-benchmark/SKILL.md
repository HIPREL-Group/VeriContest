---
name: add-leetcode-benchmark
description: Step-by-step process for adding a new LeetCode problem to the VCG-bench benchmark suite. Use this skill when asked to add, create, or scaffold a new LeetCode benchmark problem, or when working on verified Rust (Verus) solutions for LeetCode problems. The leetcode id or title-slug should be provided.
---

# Adding a New LeetCode Benchmark

Each problem lives in `benchmark/leetcode/lc<id>/` containing 7 files.

## Prerequisites

- Verus is bundled at `./verus/verus` (run from the VeriContest root) to validate proofs.
- Python 3 is needed to run the fetch script.

## Step 1: Choose a Suitable Problem

Pick a LeetCode problem that:
- Is **not** a premium/paid problem. The fetch script cannot retrieve content for
  premium problems.
- Is **not** already present in `benchmark/leetcode/` (check existing `lc*` directories).
- Is **not** recorded in `benchmark/leetcode/failed.md` as a previously attempted but abandoned problem.
- Read `supported_rust_features.md` (bundled with this skill) for details on what is currently supported in Verus. Avoid problems that require unsupported or partially supported features, as they will be difficult or impossible to verify.
- Uses only arrays/vectors, integers, and simple control flow.
- Has properties that are **amenable to formal verification** (e.g., sortedness,
  uniqueness, element preservation, index relationships, mathematical invariants).
- No `BTreeMap`, `BinaryHeap`, or other collections that Verus does not support.
- No string or float manipulation.

## Step 2: Fetch the Problem Description and Tags

Run the fetch script bundled with this skill:

```
python3 scripts/fetch_problem.py <title-slug>
```

This writes `description.md` and `tags` into this skill's own `result/lc<id>/`
folder (i.e. `skills/add-leetcode-benchmark/result/lc<id>/`) by querying
LeetCode's GraphQL API. It also prints the **Rust starter code snippet** — use this
to match the exact function name, parameter names, and return type. Move the
generated files into `benchmark/leetcode/lc<id>/` when integrating into the
benchmark suite.

**Important:** The fetch script's HTML-to-Markdown conversion may produce an ugly output that may have to be cleaned up to produce a well-formatted `description.md`.

## Step 3: Research Efficient Solutions from LeetCode Discussions

Before writing any code, fetch the top-rated community solutions from LeetCode to
understand the most efficient and well-regarded approaches for this problem.

```
python3 scripts/fetch_solutions.py <title-slug>
```

By default the script searches for Rust solutions first. If no high-rated Rust
solutions exist (fewer than 25 votes), it falls back to Python, then to all
languages.

Use the insights from community solutions to inform the algorithm you write in
Steps 6 and 7, but always ensure the implementation conforms to the Verus
constraints described in this skill.

**Always prefer the optimal solution.** Choose the algorithm with the best
time and space complexity that is feasible to verify in Verus. Avoid brute-force
or naive approaches when an efficient algorithm exists (e.g., prefer binary
search over linear scan, two-pointer over nested loops, single-pass over
multi-pass).

## Step 4: Write `spec.rs` first

Start from the problem description and encode the formal contract before writing
implementation code.

`spec.rs` should include:
- The `use vstd::prelude::*;`, `fn main() {}`, `verus! { ... }` wrapper.
- `pub struct Solution;`
- Any `spec fn` helpers needed by the specification.
- The target function with the exact signature from LeetCode starter Rust code.
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

## Step 5: Write `code.rs` and `code_spec.rs` from `spec.rs`

Implement the algorithm only after the spec is defined.

### `code.rs`
- Implement the algorithm in plain Rust using the exact signature from `spec.rs`.
- Use `impl Solution { ... }` wrapper (no `pub struct Solution;`, no `use` imports).
- Use `while` loops or `for i in 0..n` — avoid iterators, closures, and `for x in vec`.
- Use `nums[i]` indexing — no `.iter()`, `.map()`, `.filter()`, etc.
- For mutation, use direct assignment (`nums[i] = val`).
- No `match` on `Option`/`Result` unless using `checked_*` arithmetic.
- Avoid `as` casts where possible; use them only for `usize`↔`i32` at return boundaries.
- Match the time and space complexity, or other patterns, if any are suggested by the description.

### `code_spec.rs`
- Copy the algorithm from `code.rs` into Verus form while preserving behavior.
- Keep the Verus wrapper, `pub struct Solution;`, function signature, `requires`,
  `ensures`, and any helper `spec fn` from `spec.rs`.
- Do **not** include proof blocks, ghost variables, loop invariants, or decreases.
- For vector mutation in Verus code, use `nums.set(idx, val)`.

### Optional: verify `code.rs` on LeetCode

If `LEETCODE_SESSION`/`LEETCODE_CSRF_TOKEN` are set in `.env`, submit `code.rs` to
confirm it is actually Accepted:

```
python3 scripts/submit_leetcode.py submit --slug <title-slug> --code-file benchmark/leetcode/lc<id>/code.rs
```

Skip silently if credentials are missing/expired or the submission hits any
technical difficulty — this is a best-effort check, not a required step.

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
./verus/verus benchmark/leetcode/lc<id>/verified.rs --no-cheating --expand-errors --rlimit 100000
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
  value bounds, sortedness, etc.).
- **Postconditions:** Encode what the problem asks to prove (e.g., result is sorted,
  all unique elements preserved, correct count returned).
- **Triggers:** When using `forall` with `exists` inside, annotate the outer
  quantifier's body with `#[trigger]` on a suitable term (often `old(nums)[i]` or
  `nums[j]`).
- **Decreases:** Every `while` loop needs a `decreases` clause (e.g., `n - fast`).

## Step 7: Back-propagate refinements to `code.rs` and `code_spec.rs`

After `verified.rs` succeeds, align implementation files with the final verified
algorithm:

- Update `code_spec.rs` to match the verified algorithm structure (without proof, ghost vars, loop invariants, and decreases).
- Update `code.rs` to match the same final algorithm in plain Rust form.
- Keep function signatures and behavior consistent across `spec.rs`, `code_spec.rs`, `code.rs`, and `verified.rs`.

**Validate consistency by running:**
```
python3 scripts/check_consistency.py benchmark/leetcode/lc<id>
```
It must report no inconsistencies.

## Step 8: Final Cleanup and Validation

1. For `description.md`, ensure the formatting style aligns with `benchmark/leetcode/lc7/description.md`. 
2. For all code files, remove all the comments.

**Some tips:**
- For in-place mutation functions (`&mut Vec`), check the mutated vector after the call.

## File Summary

| File             | What it contains                                             |
|------------------|--------------------------------------------------------------|
| `description.md` | Problem statement in Markdown (faithful to LeetCode)         |
| `tags`           | Line 1: difficulty, Line 2: topics, Line 3: acceptance rate  |
| `code.rs`        | Plain Rust solution (no Verus, no proofs)                    |
| `spec.rs`        | Verus requires/ensures + empty body (the verification task)  |
| `code_spec.rs`   | Verus requires/ensures + algorithm body (no proofs)          |
| `verified.rs`    | Full Verus proof (must pass `verus` verification)            |

## When to Abandon a Problem

If after repeated attempts you are unable to produce a correct spec, a working
implementation, or a verifiable proof — **drop the problem and pick a different one.** Delete the partial `lc<id>/` directory and restart from Step 1. 

Not every LeetCode problem is tractable in Verus. Common reasons to abandon:
- The specification becomes circular or mirrors the implementation instead of the
  problem description.
- The proof requires non-linear arithmetic or bit-level reasoning that Verus
  cannot discharge within a reasonable resource limit.
- The optimal algorithm needs data structures or language features unsupported by
  Verus.
- Verification repeatedly times out or produces errors that resist targeted fixes.

Do not spend unbounded effort on a single problem. Move on and invest time in a problem that yields a clean spec, implementation, and proof.

## Reference Examples

For the chosen algorithm, review the examples in `examples.md` (bundled with this skill) for guidance on specification and verification strategy.
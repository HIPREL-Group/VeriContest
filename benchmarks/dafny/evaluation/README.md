# Scoring Dafny solutions

`score.py` scores one Dafny solution per problem (End2End, LeetCode and
Codeforces) against the problem's reference specification, a Dafny translation
of the Verus version's spec. The reference specifications and their translator
are currently hidden, so the maintainers score Dafny entries; this folder is
the scorer they run, and this page is the scoring policy.

```bash
VERICONTEST_DAFNY_TRANSLATOR=TRANSLATOR \
python3 benchmarks/dafny/evaluation/score.py --outputs SOLUTIONS --ref REF [--ref REF2] --vir-dir VIR \
    --tests-root TESTS --cf-tests-root CF_TESTS --out EVAL [PID ...]
```

`SOLUTIONS/<family>/<pid>.dfy` is the solution, and `TESTS` holds the test
cases of the [Hugging Face release](https://huggingface.co/datasets/Gax-c/VeriContest),
the same test cases as the Verus version's. `REF` (the reference specs, one per
family), `VIR` and `CF_TESTS` (the function-level Codeforces test cases) come
from the hidden translator. `EVAL` gets `results.jsonl` (one record per
problem, with the status of every check), `summary.json` and `eval_logs/`. The
scorer reads the Verus problems, the output checkers and the output comparison
from [`benchmarks/verus/`](../../verus/README.md).

## Interface

Each problem's description,
[`problems/<family>/<pid>/description.md`](../problems/), ends with its
starter code: the header of the entry method and the declarations of its two
contract predicates, without any content of the reference spec. A Codeforces
problem's entry methods are the functions that its Verus program's `main` calls
(one or two), and the description shows that `main` after the starter, since the
test cases are its stdin and stdout.

A solution is one file. It defines, at the top level, the two predicates and the
method with exactly the starter's header:

```dafny
predicate two_sum_pre(nums: seq<int>, target: int) { ... }
predicate two_sum_post(nums: seq<int>, target: int, res: seq<int>) requires two_sum_pre(nums, target) { ... }

method two_sum(nums: seq<int>, target: int) returns (res: seq<int>)
  requires two_sum_pre(nums, target)
  ensures two_sum_post(nums, target, res)
{ ... }
```

Only a `decreases` clause may follow the header. Attributes that only steer
proof search may precede the method's name: `{:isolate_assertions}`,
`{:vcs_split_on_every_assert}`, `{:vcs_max_cost}`, `{:vcs_max_splits}`,
`{:vcs_max_keep_going_splits}` and `{:resource_limit}`. Helpers can be anywhere
in the file, including in modules. A problem without a solution fails.

## Checks

| Check | Passes when |
|---|---|
| form | no `include` or `{:options}`; for each entry method, one `method <f>`, with the starter's header |
| audit | `dafny audit` has no findings: `assume`, `{:axiom}`, `{:extern}`, `{:verify false}`, `{:only}`, declarations without a body, `decreases *`, `forall` statements without a body |
| verify | `dafny verify --allow-warnings --enforce-determinism --verification-time-limit 0` succeeds within 600 s |
| code tests | compiled to Rust (`dafny build --target:rs`, then `cargo build --release`), the method reproduces every expected output within the per-case limit; judged by `tests/checker.py` where the problem has one, else by VeriContest's comparison (exact JSON; a Codeforces stdout as a string). LeetCode: each call of the method (`rust_harness.py`); Codeforces: each run of the program with the methods (`cf_program.py`) |
| spec tests | compiled to Python, `<f>_pre` and `<f>_post`, run on the test cases the reference spec is tested on, accept every positive case, and `<f>_post` rejects every mutated case |
| precondition | Dafny proves each `<f>_pre` equivalent to the reference precondition (`precondition.py`) |

Checks run in this order and stop at the first failure. `audit` is needed on top
of `verify`: with `--allow-warnings`, `dafny verify` accepts a lemma without a
body (an unproven assumption) and skips every member but the one marked
`{:only}`. Deterministic mode is what Dafny's Rust backend requires: without it,
an array created without an initializer is left uninitialized in the Rust code.
`--verification-time-limit 0` removes Dafny's default limit of 30 s per
verification task, so that, as for Verus, only the 600 s per problem counts.

A problem's spec tests go to human review under the
[specification review standard](../../../leaderboard/SPEC_REVIEW.md) when the
reference spec disagrees with the test cases, or the solution's pre- or
postcondition is not compilable (a ghost predicate), times out, or raises
errors.

When the reference spec cannot be tested (it is ghost or runs out of time), a
solution's spec that passes the spec tests still passes: the positive cases'
outputs are the ones the code tests use, and every mutated output is wrong, as it
differs from the problem's only answer or the problem's checker rejects it. Any
other result goes to review, since an input the solution's precondition rejects
may be outside the reference precondition too.

## Codeforces

A Codeforces test case is the stdin and stdout of the Verus version's program
(`main.rs`): its `main` reads the input, calls the entry methods
(`Solution::<f>`) and prints what they return.

- **Code tests** (`cf_program.py`): `src/bin/cfmain.rs` in the solution's Rust
  crate is that program with an `impl Solution` whose methods have the Rust
  signatures of `main.rs`. Each converts its arguments to the Dafny values of
  the method's parameters, calls the compiled method, and converts the result
  back; an integer outside the range of the Rust result type panics, which is a
  runtime error. `main` runs in a thread with a 1 GiB stack. The program runs
  on each test case's stdin, as VeriContest's Verus scorer runs `main.rs`: 1 s
  of wall clock per run, the stdout compared with the expected one as a string
  (ends trimmed) or judged by `tests/checker.py`.
- **Spec tests**: on function-level test cases: the arguments of each call that
  `main` makes on a test case's input, and the results it prints as the
  expected stdout (or as a mutated one). spec-pos checks each call; for a
  mutated stdout, some postcondition must reject one of its calls. A problem
  without function-level test cases goes to review.
- **Precondition**: each entry method's, as below.

## Preconditions

The test cases check a precondition in one direction only. Every positive input
must satisfy it, so the spec tests catch a precondition that rejects a valid
input. They never catch one that admits more than the reference's, since every
test case input is valid. So preconditions are checked by proof first, then by
review:

1. `precondition.py` puts the solution (`module Ans`) and the reference spec
   (`module Ref`) in one file. Dafny then tries to prove two lemmas, with empty
   bodies and a 60 s limit each: `AnsImpliesRef` (the solution's precondition
   implies the reference's) and `RefImpliesAns` (the converse). Both assume
   `TypeOK`, the ranges of the Verus parameter types. Inputs are compared over
   these values only.
2. If both are proved, the check passes. If not (a lemma that fails or times
   out), the precondition goes to human review. A failed proof does not mean
   that the preconditions differ, so the reviewer decides. The log names the
   reference clauses Dafny could not derive. A precondition fails the review
   when there is an input, within `TypeOK`, that one precondition admits and
   the other rejects.

Postconditions are tested first and reviewed when they cannot be tested: by the
spec tests, or by human review when the spec tests go to review.

## Limits

`LIMITS` in `score.py`. The per-case limit (`--case-timeout`, 1 s by default, as
for Verus) bounds one call of the entry method in the Rust build of a LeetCode
problem, without process start-up or conversion of the input, and one run of a
Codeforces problem's program, as Verus bounds one run of `main.rs`. The harness
runs each call in a thread with a 1 GiB stack, so deep recursion does not need
`ulimit -s`. Dafny's `int` and `seq<int>` are arbitrary-precision: on the
largest lc1 test case (n = 10000), the O(n²) solution, which is also the Verus
reference's algorithm, takes 8.7 s with them, and well under 1 s with bounded
integer types.

| Step | Limit |
|---|---|
| `dafny audit` | 300 s |
| `dafny verify` | 600 s for the whole run, no limit per verification task |
| `dafny build` and `cargo build --release` | 600 s each |
| code tests | 1 s per case; 3600 s per problem |
| spec tests | 1800 s per problem |
| precondition | 60 s per lemma; 300 s per `dafny verify` run |

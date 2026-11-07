# Specification review

SpecGen and End2End answers are first tested with post2exe: the answer's
specification is lowered into an executable checker and run on the problem's
positive test cases and mutated negative test cases (see `benchmarks/verus/evaluation/README.md`).
A problem whose specification post2exe cannot test, because the translation is
unsupported or exceeds its time limits, is reviewed against the problem's
reference `spec.rs` under the standard below.

## Preconditions

The test cases check a precondition in one direction only. Every positive test
case input must satisfy it, so a precondition that rejects a valid input fails
the spec tests. One that admits inputs the reference rejects passes them, since
every test case input is valid. So the answer's precondition is checked on every
problem:

1. **Proof.** The checker tries to prove that the answer's precondition and the
   reference precondition imply each other, over the inputs the parameter types
   can represent. If both implications are proved, the precondition passes.
2. **Review.** Otherwise the precondition is reviewed under the standard below.
   A failed proof does not mean the preconditions differ.

Postconditions are checked by the spec tests. A postcondition that cannot be
tested is reviewed under the standard below.

## Standard

- **Precondition:** the answer's precondition must be equivalent to the
  reference precondition. One that rejects an input the reference admits, or
  admits an input the reference rejects, fails.
- **Postcondition:** for every input the reference precondition admits, the
  answer's postcondition must accept exactly the outputs the reference
  postcondition accepts. Rejecting a correct output or accepting a wrong one fails.
- **Verdict:** a problem passes when both are equivalent.

A missing target function, or a target function without `ensures`, fails.
Differences in types or names do not matter when they do not change which
inputs and outputs are admitted. Outputs are compared as the problem's harness
observes them: a return field the harness never prints in a branch is not
constrained there, as in the automatic test path. A reference precondition
clause implied by its other clauses need not be restated.

## Record

Each entry's `review.json` records the final verdict for every problem.

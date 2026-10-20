# Specification review

SpecGen and End2End answers are first tested with post2exe: the answer's
specification is lowered into an executable checker and run on the problem's
positive test cases and mutated negative test cases (see `evaluation/README.md`).
A problem whose specification post2exe cannot test, because the translation is
unsupported or exceeds its time limits, is reviewed against the problem's
reference `spec.rs` under the standard below.

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

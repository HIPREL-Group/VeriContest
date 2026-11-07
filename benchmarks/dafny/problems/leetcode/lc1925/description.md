# Count Square Sum Triples

A **square triple** `(a, b, c)` is a triple where `a`, `b`, and `c` are **integers** and `a^2 + b^2 = c^2`.

Given an integer `n`, return the number of **square triples** such that `1 <= a, b, c <= n`.

## Example 1:

> **Input:** n = 5
> **Output:** 2
> **Explanation:** The square triples are (3,4,5) and (4,3,5).

## Example 2:

> **Input:** n = 10
> **Output:** 4
> **Explanation:** The square triples are (3,4,5), (4,3,5), (6,8,10), and (8,6,10).

## Constraints:

- `1 <= n <= 250`

## Starter Code

```dafny
predicate count_triples_pre(n: int)

predicate count_triples_post(n: int, result: int)
  requires count_triples_pre(n)

method count_triples(n: int) returns (result: int)
  requires count_triples_pre(n)
  ensures count_triples_post(n, result)
```

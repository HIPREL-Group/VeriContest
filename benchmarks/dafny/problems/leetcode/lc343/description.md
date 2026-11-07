# Integer Break

Given an integer `n`, break it into the sum of `k` **positive integers**, where `k >= 2`, and maximize the product of those integers.

Return *the maximum product you can get*.

## Example 1:

> **Input:** n = 2
> **Output:** 1
> **Explanation:** 2 = 1 + 1, 1 x 1 = 1.

## Example 2:

> **Input:** n = 10
> **Output:** 36
> **Explanation:** 10 = 3 + 3 + 4, 3 x 3 x 4 = 36.

## Constraints:

- `2 <= n <= 58`

## Starter Code

```dafny
predicate integer_break_pre(n: int)

predicate integer_break_post(n: int, result: int)
  requires integer_break_pre(n)

method integer_break(n: int) returns (result: int)
  requires integer_break_pre(n)
  ensures integer_break_post(n, result)
```

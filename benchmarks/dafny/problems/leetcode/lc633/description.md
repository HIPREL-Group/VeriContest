# Sum of Square Numbers

Given a non-negative integer `c`, decide whether there are two integers `a` and `b` such that `a^2 + b^2 = c`.

## Example 1

> **Input:** c = 5  
> **Output:** true  
> **Explanation:** 1 * 1 + 2 * 2 = 5

## Example 2

> **Input:** c = 3  
> **Output:** false

## Constraints

- `0 <= c <= 2^31 - 1`

## Starter Code

```dafny
predicate judge_square_sum_pre(c: int)

predicate judge_square_sum_post(c: int, result: bool)
  requires judge_square_sum_pre(c)

method judge_square_sum(c: int) returns (result: bool)
  requires judge_square_sum_pre(c)
  ensures judge_square_sum_post(c, result)
```

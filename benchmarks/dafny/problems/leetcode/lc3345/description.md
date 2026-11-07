# Smallest Divisible Digit Product I

Given two integers `n` and `t`, return the smallest integer greater than or equal to `n` such that the product of its digits is divisible by `t`.

## Example 1:

> **Input:** n = 10, t = 2
> **Output:** 10

## Example 2:

> **Input:** n = 15, t = 3
> **Output:** 16

## Constraints:

- `1 <= n <= 100`
- `1 <= t <= 10`

## Starter Code

```dafny
predicate smallest_number_pre(n: int, t: int)

predicate smallest_number_post(n: int, t: int, result: int)
  requires smallest_number_pre(n, t)

method smallest_number(n: int, t: int) returns (result: int)
  requires smallest_number_pre(n, t)
  ensures smallest_number_post(n, t, result)
```

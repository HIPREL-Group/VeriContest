# Consecutive Numbers Sum

Given an integer `n`, return the number of ways you can write `n` as the sum of consecutive positive integers.

## Example 1:

> **Input:** n = 5
> **Output:** 2
> **Explanation:** 5 = 2 + 3

## Example 2:

> **Input:** n = 9
> **Output:** 3
> **Explanation:** 9 = 4 + 5 = 2 + 3 + 4

## Example 3:

> **Input:** n = 15
> **Output:** 4
> **Explanation:** 15 = 8 + 7 = 4 + 5 + 6 = 1 + 2 + 3 + 4 + 5

## Constraints:

- $1 <= n <= 10^9$

## Starter Code

```dafny
predicate consecutive_numbers_sum_pre(n: int)

predicate consecutive_numbers_sum_post(n: int, result: int)
  requires consecutive_numbers_sum_pre(n)

method consecutive_numbers_sum(n: int) returns (result: int)
  requires consecutive_numbers_sum_pre(n)
  ensures consecutive_numbers_sum_post(n, result)
```

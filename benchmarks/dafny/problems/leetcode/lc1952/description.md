# Three Divisors

Given an integer `n`, return `true` if `n` has **exactly three positive divisors**. Otherwise, return `false`.

An integer `m` is a **divisor** of `n` if there exists an integer `k` such that `n = k * m`.

## Example 1:

> **Input:** n = 2
> **Output:** false
> **Explanation:** 2 has only two divisors: 1 and 2.

## Example 2:

> **Input:** n = 4
> **Output:** true
> **Explanation:** 4 has three divisors: 1, 2, and 4.

## Constraints:

- $1 <= n <= 10^4$

## Starter Code

```dafny
predicate is_three_pre(n: int)

predicate is_three_post(n: int, res: bool)
  requires is_three_pre(n)

method is_three(n: int) returns (res: bool)
  requires is_three_pre(n)
  ensures is_three_post(n, res)
```

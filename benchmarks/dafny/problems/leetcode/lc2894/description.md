# Divisible and Non-divisible Sums Difference

You are given positive integers `n` and `m`.

Define two integers as follows:

- `num1`: The sum of all integers in the range `[1, n]` (both **inclusive**) that are **not divisible** by `m`.
- `num2`: The sum of all integers in the range `[1, n]` (both **inclusive**) that are **divisible** by `m`.

Return *the integer* `num1 - num2`.

## Example 1:

> **Input:** `n = 10`, `m = 3`
> **Output:** `19`
> **Explanation:** 
> - Integers not divisible by 3: `[1,2,4,5,7,8,10]`, sum is 37.
> - Integers divisible by 3: `[3,6,9]`, sum is 18.
> We return `37 - 18 = 19`.

## Constraints:

- `1 <= n, m <= 1000`

## Starter Code

```dafny
predicate difference_of_sums_pre(n: int, m: int)

predicate difference_of_sums_post(n: int, m: int, result: int)
  requires difference_of_sums_pre(n, m)

method difference_of_sums(n: int, m: int) returns (result: int)
  requires difference_of_sums_pre(n, m)
  ensures difference_of_sums_post(n, m, result)
```

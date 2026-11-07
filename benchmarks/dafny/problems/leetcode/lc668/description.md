# Kth Smallest Number in Multiplication Table

Nearly everyone has used the [Multiplication Table](https://en.wikipedia.org/wiki/Multiplication_table). The multiplication table of size `m x n` is an integer matrix `mat` where `mat[i][j] == i * j` (**1-indexed**).

Given three integers `m`, `n`, and `k`, return *the *`k^th`* smallest element in the *`m x n`* multiplication table*.

## Example 1:

> **Input:** m = 3, n = 3, k = 5
> **Output:** 3
> **Explanation:** The 5^th smallest number is 3.

## Example 2:

> **Input:** m = 2, n = 3, k = 6
> **Output:** 6
> **Explanation:** The 6^th smallest number is 6.

## Constraints:

- `1 <= m, n <= 3 * 10^4`
- `1 <= k <= m * n`

## Starter Code

```dafny
predicate find_kth_number_pre(m: int, n: int, k: int)

predicate find_kth_number_post(m: int, n: int, k: int, result: int)
  requires find_kth_number_pre(m, n, k)

method find_kth_number(m: int, n: int, k: int) returns (result: int)
  requires find_kth_number_pre(m, n, k)
  ensures find_kth_number_post(m, n, k, result)
```

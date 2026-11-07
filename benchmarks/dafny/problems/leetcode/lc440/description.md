# K-th Smallest in Lexicographical Order

Given two integers `n` and `k`, return *the* `k^th` *lexicographically smallest integer in the range* `[1, n]`.

## Example 1:

> **Input:** n = 13, k = 2
> **Output:** 10
> **Explanation:** The lexicographical order is [1, 10, 11, 12, 13, 2, 3, 4, 5, 6, 7, 8, 9], so the second smallest number is 10.

## Example 2:

> **Input:** n = 1, k = 1
> **Output:** 1

## Constraints:

- `1 <= k <= n <= 10^9`

## Starter Code

```dafny
predicate find_kth_number_pre(n: int, k: int)

predicate find_kth_number_post(n: int, k: int, result: int)
  requires find_kth_number_pre(n, k)

method find_kth_number(n: int, k: int) returns (result: int)
  requires find_kth_number_pre(n, k)
  ensures find_kth_number_post(n, k, result)
```

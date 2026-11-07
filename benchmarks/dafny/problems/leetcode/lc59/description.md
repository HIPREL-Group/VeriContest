# Spiral Matrix II

Given a positive integer `n`, return an `n x n` matrix filled with the integers from `1` to `n^2` in spiral order.

## Example 1:

> **Input:** n = 3
> **Output:** [[1,2,3],[8,9,4],[7,6,5]]

## Example 2:

> **Input:** n = 1
> **Output:** [[1]]

## Constraints:

- `1 <= n <= 20`

## Starter Code

```dafny
predicate generate_matrix_pre(n: int)

predicate generate_matrix_post(n: int, res: seq<seq<int>>)
  requires generate_matrix_pre(n)

method generate_matrix(n: int) returns (res: seq<seq<int>>)
  requires generate_matrix_pre(n)
  ensures generate_matrix_post(n, res)
```

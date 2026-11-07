# Matrix Diagonal Sum

Given a square matrix `mat`, return the sum of the matrix diagonals.

Only include the sum of all the elements on the primary diagonal and all the elements on the secondary diagonal that are not part of the primary diagonal.

## Example 1:

> **Input:** mat = [[1,2,3],[4,5,6],[7,8,9]]
> **Output:** 25
> **Explanation:** Diagonals sum: 1 + 5 + 9 + 3 + 7 = 25. Notice that element mat[1][1] = 5 is counted only once.

## Example 2:

> **Input:** mat = [[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,1,1]]
> **Output:** 8

## Example 3:

> **Input:** mat = [[5]]
> **Output:** 5

## Constraints:

- `n == mat.length == mat[i].length`
- $1 \leq n \leq 100$
- $1 \leq mat[i][j] \leq 100$

## Starter Code

```dafny
predicate diagonal_sum_pre(mat: seq<seq<int>>)

predicate diagonal_sum_post(mat: seq<seq<int>>, result: int)
  requires diagonal_sum_pre(mat)

method diagonal_sum(mat: seq<seq<int>>) returns (result: int)
  requires diagonal_sum_pre(mat)
  ensures diagonal_sum_post(mat, result)
```

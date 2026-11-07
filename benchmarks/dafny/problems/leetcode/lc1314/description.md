# Matrix Block Sum

Given a `m x n` matrix `mat` and an integer `k`, return a matrix `answer` where each `answer[i][j]` is the sum of all elements `mat[r][c]` for:

- `i - k <= r <= i + k`,
- `j - k <= c <= j + k`, and
- `(r, c)` is a valid position in the matrix.

## Example 1:

> **Input:** mat = [[1,2,3],[4,5,6],[7,8,9]], k = 1
> **Output:** [[12,21,16],[27,45,33],[24,39,28]]

## Example 2:

> **Input:** mat = [[1,2,3],[4,5,6],[7,8,9]], k = 2
> **Output:** [[45,45,45],[45,45,45],[45,45,45]]

## Constraints:

- $m == mat.length$
- $n == mat[i].length$
- $1 <= m, n, k <= 100$
- $1 <= mat[i][j] <= 100$

## Starter Code

```dafny
predicate matrix_block_sum_pre(mat: seq<seq<int>>, k: int)

predicate matrix_block_sum_post(mat: seq<seq<int>>, k: int, answer: seq<seq<int>>)
  requires matrix_block_sum_pre(mat, k)

method matrix_block_sum(mat: seq<seq<int>>, k: int) returns (answer: seq<seq<int>>)
  requires matrix_block_sum_pre(mat, k)
  ensures matrix_block_sum_post(mat, k, answer)
```

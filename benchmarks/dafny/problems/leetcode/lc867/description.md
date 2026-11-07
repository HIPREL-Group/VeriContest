# Transpose Matrix

Given a 2D integer array `matrix`, return the transpose of `matrix`.

The transpose of a matrix is the matrix flipped over its main diagonal, switching the matrix's row and column indices.

## Example 1:

> **Input:** matrix = [[1,2,3],[4,5,6],[7,8,9]]
> **Output:** [[1,4,7],[2,5,8],[3,6,9]]

## Example 2:

> **Input:** matrix = [[1,2,3],[4,5,6]]
> **Output:** [[1,4],[2,5],[3,6]]

## Constraints:

- $m == matrix.length$
- $n == matrix[i].length$
- $1 <= m, n <= 1000$
- $1 <= m * n <= 10^5$
- $-10^9 <= matrix[i][j] <= 10^9$

## Starter Code

```dafny
predicate transpose_pre(matrix: seq<seq<int>>)

predicate transpose_post(matrix: seq<seq<int>>, res: seq<seq<int>>)
  requires transpose_pre(matrix)

method transpose(matrix: seq<seq<int>>) returns (res: seq<seq<int>>)
  requires transpose_pre(matrix)
  ensures transpose_post(matrix, res)
```

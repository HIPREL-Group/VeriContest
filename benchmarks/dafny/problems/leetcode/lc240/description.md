# Search a 2D Matrix II

Write an efficient algorithm that searches for a value `target` in an `m x n` integer matrix `matrix`. This matrix has the following properties:

- Integers in each row are sorted in ascending from left to right.

- Integers in each column are sorted in ascending from top to bottom.

## Example 1:
> **Input:** matrix = [[1,4,7,11,15],[2,5,8,12,19],[3,6,9,16,22],[10,13,14,17,24],[18,21,23,26,30]], target = 5
> **Output:** true


## Example 2:
> **Input:** matrix = [[1,4,7,11,15],[2,5,8,12,19],[3,6,9,16,22],[10,13,14,17,24],[18,21,23,26,30]], target = 20
> **Output:** false

## Constraints:

- $m == matrix.length$

- $n == matrix[i].length$

- $1 <= n, m <= 300$

- $-10^9 <= matrix[i][j] <= 10^9$

- All the integers in each row are sorted in ascending order.

- All the integers in each column are sorted in ascending order.

- $-10^9 <= target <= 10^9$

## Starter Code

```dafny
predicate search_matrix_pre(matrix: seq<seq<int>>, target: int)

predicate search_matrix_post(matrix: seq<seq<int>>, target: int, res: bool)
  requires search_matrix_pre(matrix, target)

method search_matrix(matrix: seq<seq<int>>, target: int) returns (res: bool)
  requires search_matrix_pre(matrix, target)
  ensures search_matrix_post(matrix, target, res)
```

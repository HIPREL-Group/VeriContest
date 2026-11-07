# Diagonal Traverse

Given an `m x n` matrix `mat`, return *an array of all the elements of the array in a diagonal order*.

## Example 1:

> **Input:** mat = [[1,2,3],[4,5,6],[7,8,9]]
> **Output:** [1,2,4,7,5,3,6,8,9]

## Example 2:

> **Input:** mat = [[1,2],[3,4]]
> **Output:** [1,2,3,4]

## Constraints:

- `m == mat.length`
- `n == mat[i].length`
- `1 <= m, n <= 10^4`
- `1 <= m * n <= 10^4`
- `-10^5 <= mat[i][j] <= 10^5`

## Starter Code

```dafny
predicate find_diagonal_order_pre(mat: seq<seq<int>>)

predicate find_diagonal_order_post(mat: seq<seq<int>>, result: seq<int>)
  requires find_diagonal_order_pre(mat)

method find_diagonal_order(mat: seq<seq<int>>) returns (result: seq<int>)
  requires find_diagonal_order_pre(mat)
  ensures find_diagonal_order_post(mat, result)
```

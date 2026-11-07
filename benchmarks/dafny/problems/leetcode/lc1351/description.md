# Count Negative Numbers in a Sorted Matrix

You are given an `m x n` matrix `grid` sorted in non-increasing order both row-wise and column-wise.

Return the number of negative numbers in `grid`.

## Example 1:

> **Input:** grid = [[4,3,2,-1],[3,2,1,-1],[1,1,-1,-2],[-1,-1,-2,-3]]
> **Output:** 8
> **Explanation:** There are 8 negative numbers in the matrix.

## Example 2:

> **Input:** grid = [[3,2],[1,0]]
> **Output:** 0

## Constraints:

- $m == grid.length$

- $n == grid[i].length$

- $1 <= m, n <= 100$

- $-100 <= grid[i][j] <= 100$

## Starter Code

```dafny
predicate count_negatives_pre(grid: seq<seq<int>>)

predicate count_negatives_post(grid: seq<seq<int>>, res: int)
  requires count_negatives_pre(grid)

method count_negatives(grid: seq<seq<int>>) returns (res: int)
  requires count_negatives_pre(grid)
  ensures count_negatives_post(grid, res)
```

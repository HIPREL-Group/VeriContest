# Check if Grid Satisfies Conditions

You are given a 2D matrix `grid` of size `m x n`. You need to check whether each cell `grid[i][j]` satisfies the following conditions:

- If the cell below it exists, then `grid[i][j] == grid[i + 1][j]`.
- If the cell to its right exists, then `grid[i][j] != grid[i][j + 1]`.

Return `true` if all the cells satisfy these conditions. Otherwise, return `false`.

## Example 1:

> **Input:** grid = [[1,0,2],[1,0,2]]
> **Output:** true

## Example 2:

> **Input:** grid = [[1,1,1],[0,0,0]]
> **Output:** false

## Example 3:

> **Input:** grid = [[1],[2],[3]]
> **Output:** false

## Constraints:

- `1 <= n, m <= 10`
- `0 <= grid[i][j] <= 9`

## Starter Code

```dafny
predicate satisfies_conditions_pre(grid: seq<seq<int>>)

predicate satisfies_conditions_post(grid: seq<seq<int>>, result: bool)
  requires satisfies_conditions_pre(grid)

method satisfies_conditions(grid: seq<seq<int>>) returns (result: bool)
  requires satisfies_conditions_pre(grid)
  ensures satisfies_conditions_post(grid, result)
```

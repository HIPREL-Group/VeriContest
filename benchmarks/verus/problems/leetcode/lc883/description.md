# Projection Area of 3D Shapes

You are given an `n x n` `grid` where we place some `1 x 1 x 1` cubes that are axis-aligned with the `x`, `y`, and `z` axes.

Each value `grid[i][j]` represents a tower of `grid[i][j]` cubes placed on top of the cell `(i, j)`.

We view the projection of these cubes onto the `xy`, `yz`, and `zx` planes.

Return the total area of all three projections.

## Example 1:

> **Input:** grid = [[1,2],[3,4]]
> **Output:** 17

## Example 2:

> **Input:** grid = [[2]]
> **Output:** 5

## Example 3:

> **Input:** grid = [[1,0],[0,2]]
> **Output:** 8

## Constraints:

- `n == grid.length == grid[i].length`
- `1 <= n <= 50`
- `0 <= grid[i][j] <= 50`

## Starter Code

```rust
impl Solution {
    pub fn projection_area(grid: Vec<Vec<i32>>) -> i32 {
        
    }
}
```

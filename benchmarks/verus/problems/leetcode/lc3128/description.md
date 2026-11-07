# Right Triangles

You are given a 2D boolean matrix `grid`.

A collection of 3 elements of `grid` is a **right triangle** if one element is in the **same row** as another element and in the **same column** as the third element. The 3 elements do **not** need to be adjacent.

Return the number of right triangles formed by 3 elements of `grid` such that all 3 elements have value `1`.

## Example 1

> **Input:** `grid = [[0,1,0],[0,1,1],[0,1,0]]`
> **Output:** `2`

## Example 2

> **Input:** `grid = [[1,0,0,0],[0,1,0,1],[1,0,0,0]]`
> **Output:** `0`

## Example 3

> **Input:** `grid = [[1,0,1],[1,0,0],[1,0,0]]`
> **Output:** `2`

## Constraints

- `1 <= grid.length <= 1000`
- `1 <= grid[i].length <= 1000`
- `0 <= grid[i][j] <= 1`

## Starter Code

```rust
impl Solution {
    pub fn number_of_right_triangles(grid: Vec<Vec<i32>>) -> i64 {
        
    }
}
```

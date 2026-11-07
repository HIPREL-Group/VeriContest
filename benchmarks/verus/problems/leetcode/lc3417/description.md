# Zigzag Grid Traversal With Skip

You are given an `m x n` 2D array `grid` of positive integers.

Traverse the grid in zigzag order while skipping every alternate cell.

Zigzag traversal means:

- Start at `(0, 0)`.
- Traverse row `0` from left to right.
- Traverse row `1` from right to left.
- Continue alternating direction for each next row.

Collect visited values in order, but keep only every alternate visited cell, starting with the first visited cell.

Return the resulting array.

## Example 1

> **Input:** `grid = [[1,2],[3,4]]`
> **Output:** `[1,4]`
> **Explanation:** Zigzag order is `[1,2,4,3]`; taking alternate cells gives `[1,4]`.

## Example 2

> **Input:** `grid = [[2,1],[2,1],[2,1]]`
> **Output:** `[2,1,2]`
> **Explanation:** Zigzag order is `[2,1,1,2,2,1]`; taking alternate cells gives `[2,1,2]`.

## Example 3

> **Input:** `grid = [[1,2,3],[4,5,6],[7,8,9]]`
> **Output:** `[1,3,5,7,9]`
> **Explanation:** Zigzag order is `[1,2,3,6,5,4,7,8,9]`; taking alternate cells gives `[1,3,5,7,9]`.

## Constraints

- `2 <= n == grid.length <= 50`
- `2 <= m == grid[i].length <= 50`
- `1 <= grid[i][j] <= 2500`

## Starter Code

```rust
impl Solution {
    pub fn zigzag_traversal(grid: Vec<Vec<i32>>) -> Vec<i32> {
        
    }
}
```

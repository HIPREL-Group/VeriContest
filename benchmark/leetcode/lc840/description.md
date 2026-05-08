# Magic Squares In Grid

A `3 x 3` magic square is a `3 x 3` grid filled with distinct numbers from `1` to `9` such that each row, column, and both diagonals all have the same sum.

Given a `row x col` integer matrix `grid`, return the number of `3 x 3` magic square subgrids of `grid`.

Note that although a magic square can contain only numbers from `1` to `9`, the input grid may contain values up to `15`.

## Example 1

**Input:** `grid = [[4,3,8,4],[9,5,1,9],[2,7,6,2]]`

**Output:** `1`

## Example 2

**Input:** `grid = [[8]]`

**Output:** `0`

## Constraints

- `row == grid.length`
- `col == grid[i].length`
- `1 <= row, col <= 10`
- `0 <= grid[i][j] <= 15`

## Starter Code

```rust
impl Solution {
    pub fn num_magic_squares_inside(grid: Vec<Vec<i32>>) -> i32 {
        
    }
}
```

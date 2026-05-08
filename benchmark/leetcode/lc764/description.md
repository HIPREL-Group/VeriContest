# Largest Plus Sign

You are given an integer `n`. You have an `n x n` binary grid with all values initially `1` except for some indices given in the array `mines`. The i-th element of `mines` is `[x_i, y_i]` where `grid[x_i][y_i] == 0`.

Return the order of the largest **axis-aligned** plus sign of `1`'s contained in the grid. If there is none, return `0`.

An **axis-aligned plus sign** of `1`'s of order `k` has a center `grid[r][c] == 1` and four arms of length `k - 1` each (up, down, left, right), all made of `1`'s.

## Example 1

> **Input:** n = 5, mines = [[4,2]]  
> **Output:** 2  
> **Explanation:** The largest plus sign can only be of order 2.

## Example 2

> **Input:** n = 1, mines = [[0,0]]  
> **Output:** 0  
> **Explanation:** There is no plus sign, so return 0.

## Constraints

- `1 <= n <= 500`
- `1 <= mines.length <= 5000`
- `0 <= x_i, y_i < n`
- All pairs `(x_i, y_i)` are unique.

## Starter Code

```rust
impl Solution {
    pub fn order_of_largest_plus_sign(n: i32, mines: Vec<Vec<i32>>) -> i32 {
        
    }
}
```

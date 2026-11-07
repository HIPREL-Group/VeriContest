# Maximum Sum of an Hourglass

You are given an `m x n` integer matrix `grid`.

We define an **hourglass** as a part of the matrix with the following form:

```
a b c
  d
e f g
```

Return the **maximum** sum of the elements of an hourglass.

An hourglass cannot be rotated and must be entirely contained within the matrix.

## Example 1:

> **Input:** `grid = [[6,2,1,3],[4,2,1,5],[9,2,8,7],[4,1,2,9]]`
> 
> **Output:** `30`
> 
> **Explanation:** The hourglass with maximum sum is `6 + 2 + 1 + 2 + 9 + 2 + 8 = 30`.

## Example 2:

> **Input:** `grid = [[1,2,3],[4,5,6],[7,8,9]]`
> 
> **Output:** `35`
> 
> **Explanation:** There is only one hourglass, and its sum is `1 + 2 + 3 + 5 + 7 + 8 + 9 = 35`.

## Constraints:

- `m == grid.length`
- `n == grid[i].length`
- `3 <= m, n <= 150`
- `0 <= grid[i][j] <= 10^6`

## Starter Code

```rust
impl Solution {
    pub fn max_sum(grid: Vec<Vec<i32>>) -> i32 {
        
    }
}
```

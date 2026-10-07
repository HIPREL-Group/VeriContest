# Reconstruct a 2-Row Binary Matrix

You are given:

- A binary matrix with `2` rows and `n` columns.
- The sum of the upper row, `upper`.
- The sum of the lower row, `lower`.
- An array `colsum` where `colsum[i]` is the sum of the two cells in column `i`.

Return any binary `2 x n` matrix that satisfies these row and column sums.

If multiple valid answers exist, return any of them. If no valid matrix exists, return an empty 2D array.

## Example 1:

> **Input:** `upper = 2`, `lower = 1`, `colsum = [1,1,1]`
> **Output:** `[[1,1,0],[0,0,1]]`
> **Explanation:** `[[1,0,1],[0,1,0]]` and `[[0,1,1],[1,0,0]]` are also correct.

## Example 2:

> **Input:** `upper = 2`, `lower = 3`, `colsum = [2,2,1,1]`
> **Output:** `[]`

## Example 3:

> **Input:** `upper = 5`, `lower = 5`, `colsum = [2,1,2,0,1,0,1,2,0,1]`
> **Output:** `[[1,1,1,0,1,0,0,1,0,0],[1,0,1,0,0,0,1,1,0,1]]`

## Constraints:

- `1 <= colsum.length <= 10^5`
- `0 <= upper, lower <= colsum.length`
- `0 <= colsum[i] <= 2`

## Starter Code

```rust
impl Solution {
    pub fn reconstruct_matrix(upper: i32, lower: i32, colsum: Vec<i32>) -> Vec<Vec<i32>> {
        
    }
}
```

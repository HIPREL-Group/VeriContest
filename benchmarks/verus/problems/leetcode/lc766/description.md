# Toeplitz Matrix

Given an `m x n` matrix `matrix`, return `true` if the matrix is Toeplitz. Otherwise, return `false`.

A matrix is **Toeplitz** if every diagonal from top-left to bottom-right has the same elements.

## Example 1:

> **Input:** matrix = [[1,2,3,4],[5,1,2,3],[9,5,1,2]]
> **Output:** true
> **Explanation:** The diagonals are `[9]`, `[5, 5]`, `[1, 1, 1]`, `[2, 2, 2]`, `[3, 3]`, and `[4]`. Every diagonal has the same value in each position.

## Example 2:

> **Input:** matrix = [[1,2],[2,2]]
> **Output:** false
> **Explanation:** The diagonal `[1, 2]` contains different values.

## Constraints:

- `m == matrix.length`
- `n == matrix[i].length`
- `1 <= m, n <= 20`
- `0 <= matrix[i][j] <= 99`

## Starter Code

```rust
impl Solution {
    pub fn is_toeplitz_matrix(matrix: Vec<Vec<i32>>) -> bool {
        
    }
}
```

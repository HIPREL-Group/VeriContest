# Count Square Submatrices with All Ones

Given a `m * n` matrix of ones and zeros, return how many **square** submatrices have all ones.

## Example 1:

> **Input:** matrix = [[0,1,1,1],[1,1,1,1],[0,1,1,1]]
> **Output:** 15
> **Explanation:**
> There are **10** squares of side 1.
> There are **4** squares of side 2.
> There is **1** square of side 3.
> Total number of squares = 10 + 4 + 1 = **15**.

## Example 2:

> **Input:** matrix = [[1,0,1],[1,1,0],[1,1,0]]
> **Output:** 7
> **Explanation:**
> There are **6** squares of side 1.
> There is **1** square of side 2.
> Total number of squares = 6 + 1 = **7**.

## Constraints:

- `1 <= m <= 300`
- `1 <= n <= 300`
- `0 <= matrix[i][j] <= 1`

## Starter Code

```rust
impl Solution {
    pub fn count_squares(matrix: Vec<Vec<i32>>) -> i32 {
        
    }
}
```

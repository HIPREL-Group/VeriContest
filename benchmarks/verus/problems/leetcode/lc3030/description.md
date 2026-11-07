# Find the Grid of Region Average

You are given an `m x n` grid `image` representing a grayscale image, where `image[i][j]` is a pixel intensity in `[0, 255]`. You are also given a non-negative integer `threshold`.

Two pixels are adjacent if they share an edge.

A region is a `3 x 3` subgrid such that the absolute difference in intensity between every pair of adjacent pixels in that subgrid is at most `threshold`.

A pixel may belong to multiple regions.

Define an `m x n` grid `result`:

- If `image[i][j]` belongs to no valid region, then `result[i][j] = image[i][j]`.
- Otherwise, for each valid region containing `(i, j)`, compute that region's average intensity rounded down. Then `result[i][j]` is the rounded-down average of those rounded-down region averages.

Return `result`.

## Example 1:

> **Input:** image = [[5,6,7,10],[8,9,10,10],[11,12,13,10]], threshold = 3
> **Output:** [[9,9,9,9],[9,9,9,9],[9,9,9,9]]

## Example 2:

> **Input:** image = [[10,20,30],[15,25,35],[20,30,40],[25,35,45]], threshold = 12
> **Output:** [[25,25,25],[27,27,27],[27,27,27],[30,30,30]]

## Example 3:

> **Input:** image = [[5,6,7],[8,9,10],[11,12,13]], threshold = 1
> **Output:** [[5,6,7],[8,9,10],[11,12,13]]

## Constraints:

- `3 <= m, n <= 500`
- `0 <= image[i][j] <= 255`
- `0 <= threshold <= 255`

## Starter Code

```rust
impl Solution {
    pub fn result_grid(image: Vec<Vec<i32>>, threshold: i32) -> Vec<Vec<i32>> {
        
    }
}
```

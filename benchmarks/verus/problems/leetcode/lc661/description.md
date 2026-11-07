# Image Smoother

An image smoother is a filter of size `3 x 3` that can be applied to each cell of an image by rounding down the average of the cell and the eight surrounding cells. If a cell has fewer than eight surrounding cells, then only the existing cells are included in the average.

Given an `m x n` integer matrix `img` representing the grayscale of an image, return the image after applying the smoother to each cell.

## Example 1:

> **Input:** img = [[1,1,1],[1,0,1],[1,1,1]]
> **Output:** [[0,0,0],[0,0,0],[0,0,0]]
> **Explanation:**
> For the points (0,0), (0,2), (2,0), (2,2), floor(3 / 4) = 0.
> For the points (0,1), (1,0), (1,2), (2,1), floor(5 / 6) = 0.
> For the point (1,1), floor(8 / 9) = 0.

## Example 2:

> **Input:** img = [[100,200,100],[200,50,200],[100,200,100]]
> **Output:** [[137,141,137],[141,138,141],[137,141,137]]
> **Explanation:**
> For the points (0,0), (0,2), (2,0), (2,2), floor((100 + 200 + 200 + 50) / 4) = 137.
> For the points (0,1), (1,0), (1,2), (2,1), floor((200 + 200 + 50 + 200 + 100 + 100) / 6) = 141.
> For the point (1,1), floor((50 + 200 + 200 + 200 + 200 + 100 + 100 + 100 + 100) / 9) = 138.

## Constraints:

- `m == img.length`
- `n == img[i].length`
- `1 <= m, n <= 200`
- `0 <= img[i][j] <= 255`

## Starter Code

```rust
impl Solution {
    pub fn image_smoother(img: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        
    }
}
```

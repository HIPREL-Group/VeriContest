# Find the Number of Ways to Place People I

You are given a 2D array `points` of size `n x 2` representing integer coordinates of some points on a 2D plane, where `points[i] = [x_i, y_i]`.

Count the number of pairs of points `(A, B)`, where

- `A` is on the upper-left side of `B`.

- There are no other points in the rectangle (or line) they make, including the border, except points `A` and `B`.

Return the count.

## Example 1:

> **Input:** points = [[1,1],[2,2],[3,3]]  
> **Output:** 0

## Example 2:

> **Input:** points = [[6,2],[4,4],[2,6]]  
> **Output:** 2

## Example 3:

> **Input:** points = [[3,1],[1,3],[1,1]]  
> **Output:** 2

## Constraints:

- `2 <= n <= 50`
- `points[i].length == 2`
- `0 <= points[i][0], points[i][1] <= 50`
- All `points[i]` are distinct.

## Starter Code

```rust
impl Solution {
    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> i32 {
        
    }
}
```

# Minimum Rectangles to Cover Points

You are given a 2D integer array `points`, where `points[i] = [x_i, y_i]`, and an integer `w`.

You need to cover all points with axis-aligned rectangles. Each rectangle has lower-left corner `(x_1, 0)` and upper-right corner `(x_2, y_2)`, where `x_1 <= x_2`, `y_2 >= 0`, and `x_2 - x_1 <= w`.

A point is covered if it lies inside or on the boundary of at least one rectangle.

Return the minimum number of rectangles needed to cover all points.

A point may be covered by more than one rectangle.

## Examples

**Example 1:**
Input: points = [[2,1],[1,0],[1,4],[1,8],[3,5],[4,6]], w = 1
Output: 2
Explanation:
One optimal placement uses rectangles spanning x-ranges [1,2] and [3,4].

**Example 2:**
Input: points = [[0,0],[1,1],[2,2],[3,3],[4,4],[5,5],[6,6]], w = 2
Output: 3
Explanation:
One optimal placement uses rectangles spanning x-ranges [0,2], [3,5], and [6,6].

**Example 3:**
Input: points = [[2,3],[1,2]], w = 0
Output: 2

## Constraints

- `1 <= points.length <= 10^5`
- `points[i].length == 2`
- `0 <= x_i, y_i <= 10^9`
- `0 <= w <= 10^9`
- All pairs `(x_i, y_i)` are distinct.

## Starter Code

```rust
impl Solution {
    pub fn min_rectangles_to_cover_points(points: Vec<Vec<i32>>, w: i32) -> i32 {
        
    }
}
```

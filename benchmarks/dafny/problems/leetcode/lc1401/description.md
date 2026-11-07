# Circle and Rectangle Overlapping

You are given a circle represented as `(radius, xCenter, yCenter)` and an axis-aligned rectangle represented as `(x1, y1, x2, y2)`, where `(x1, y1)` are the coordinates of the bottom-left corner, and `(x2, y2)` are the coordinates of the top-right corner of the rectangle.

Return `true` if the circle and rectangle are overlapped otherwise return `false`. In other words, check if there is **any** point `(xi, yi)` that belongs to the circle and the rectangle at the same time.

## Example 1:

> **Input:** radius = 1, xCenter = 0, yCenter = 0, x1 = 1, y1 = -1, x2 = 3, y2 = 1
> **Output:** true
> **Explanation:** Circle and rectangle share the point (1,0).

## Example 2:

> **Input:** radius = 1, xCenter = 1, yCenter = 1, x1 = 1, y1 = -3, x2 = 2, y2 = -1
> **Output:** false

## Example 3:

> **Input:** radius = 1, xCenter = 0, yCenter = 0, x1 = -1, y1 = 0, x2 = 0, y2 = 1
> **Output:** true

## Constraints:

- `1 <= radius <= 2000`
- `-10^4 <= xCenter, yCenter <= 10^4`
- `-10^4 <= x1 < x2 <= 10^4`
- `-10^4 <= y1 < y2 <= 10^4`

## Starter Code

```dafny
predicate check_overlap_pre(radius: int, x_center: int, y_center: int, x1: int, y1: int, x2: int, y2: int)

predicate check_overlap_post(radius: int, x_center: int, y_center: int, x1: int, y1: int, x2: int, y2: int, res: bool)
  requires check_overlap_pre(radius, x_center, y_center, x1, y1, x2, y2)

method check_overlap(radius: int, x_center: int, y_center: int, x1: int, y1: int, x2: int, y2: int) returns (res: bool)
  requires check_overlap_pre(radius, x_center, y_center, x1, y1, x2, y2)
  ensures check_overlap_post(radius, x_center, y_center, x1, y1, x2, y2, res)
```

# Valid Boomerang

Given an array `points` where `points[i] = [x_i, y_i]` represents a point on the **X-Y** plane, return `true` if these points are a **boomerang**.

A **boomerang** is a set of three points that are **all distinct** and **not in a straight line**.

## Example 1:

> **Input:** points = [[1,1],[2,3],[3,2]]
> **Output:** true

## Example 2:

> **Input:** points = [[1,1],[2,2],[3,3]]
> **Output:** false

## Constraints:

- `points.length == 3`
- `points[i].length == 2`
- `0 <= x_i, y_i <= 100`

## Starter Code

```dafny
predicate is_boomerang_pre(points: seq<seq<int>>)

predicate is_boomerang_post(points: seq<seq<int>>, res: bool)
  requires is_boomerang_pre(points)

method is_boomerang(points: seq<seq<int>>) returns (res: bool)
  requires is_boomerang_pre(points)
  ensures is_boomerang_post(points, res)
```

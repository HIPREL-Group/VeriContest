# Maximum Distance in Arrays

Given `m` arrays, where each array is sorted in ascending order, return the maximum distance between any two integers chosen from two different arrays.

The distance between two integers `a` and `b` is `|a - b|`.

## Example 1:

> **Input:** arrays = [[1,2,3],[4,5],[1,2,3]]
> **Output:** 4
> **Explanation:** One way to achieve the maximum distance of 4 is to pick `1` from the first or third array and `5` from the second array.

## Example 2:

> **Input:** arrays = [[1],[1]]
> **Output:** 0

## Constraints:

- `m == arrays.length`
- `2 <= m <= 10^5`
- `1 <= arrays[i].length <= 500`
- `-10^4 <= arrays[i][j] <= 10^4`
- `arrays[i]` is sorted in ascending order.
- There will be at most `10^5` integers in all the arrays.

## Starter Code

```dafny
predicate max_distance_pre(arrays: seq<seq<int>>)

predicate max_distance_post(arrays: seq<seq<int>>, result: int)
  requires max_distance_pre(arrays)

method max_distance(arrays: seq<seq<int>>) returns (result: int)
  requires max_distance_pre(arrays)
  ensures max_distance_post(arrays, result)
```

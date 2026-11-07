# Minimum Absolute Difference

Given an array of **distinct** integers `arr`, find all pairs of elements with the minimum absolute difference of any two elements.

Return a list of pairs in ascending order (with respect to pairs), each pair `[a, b]` follows:

- `a, b` are from `arr`
- `a < b`
- `b - a` equals to the minimum absolute difference of any two elements in `arr`

## Example 1:

> **Input:** arr = [4,2,1,3]
> **Output:** [[1,2],[2,3],[3,4]]
> **Explanation:** The minimum absolute difference is 1. List all pairs with difference equal to 1 in ascending order.

## Example 2:

> **Input:** arr = [1,3,6,10,15]
> **Output:** [[1,3]]

## Example 3:

> **Input:** arr = [3,8,-10,23,19,-4,-14,27]
> **Output:** [[-14,-10],[19,23],[23,27]]

## Constraints:

- $2 <= arr.length <= 10^5$
- $-10^6 <= arr[i] <= 10^6$

## Starter Code

```dafny
predicate minimum_abs_difference_pre(arr: seq<int>)

predicate minimum_abs_difference_post(arr: seq<int>, res: seq<seq<int>>)
  requires minimum_abs_difference_pre(arr)

method minimum_abs_difference(arr: seq<int>) returns (res: seq<seq<int>>)
  requires minimum_abs_difference_pre(arr)
  ensures minimum_abs_difference_post(arr, res)
```

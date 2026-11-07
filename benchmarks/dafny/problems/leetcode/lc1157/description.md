# Online Majority Element In Subarray

Given an array `arr`, find the **majority element** of a given subarray. The **majority element** of a subarray is an element that occurs `threshold` times or more in the subarray.

Given `arr`, `left`, `right`, and `threshold`, return the element in the subarray `arr[left...right]` that occurs at least `threshold` times, or `-1` if no such element exists.

## Example 1:

> **Input:** arr = [1, 1, 2, 2, 1, 1], left = 0, right = 5, threshold = 4
> **Output:** 1

## Example 2:

> **Input:** arr = [1, 1, 2, 2, 1, 1], left = 0, right = 3, threshold = 3
> **Output:** -1

## Example 3:

> **Input:** arr = [1, 1, 2, 2, 1, 1], left = 2, right = 3, threshold = 2
> **Output:** 2

## Constraints:

- $1 \leq arr.length \leq 2 * 10^4$
- $1 \leq arr[i] \leq 2 * 10^4$
- $0 \leq left \leq right < arr.length$
- $threshold \leq right - left + 1$
- $2 * threshold > right - left + 1$

## Starter Code

```dafny
predicate query_pre(arr: seq<int>, left: int, right: int, threshold: int)

predicate query_post(arr: seq<int>, left: int, right: int, threshold: int, result: int)
  requires query_pre(arr, left, right, threshold)

method query(arr: seq<int>, left: int, right: int, threshold: int) returns (result: int)
  requires query_pre(arr, left, right, threshold)
  ensures query_post(arr, left, right, threshold, result)
```

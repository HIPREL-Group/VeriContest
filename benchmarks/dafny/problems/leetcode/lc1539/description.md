# Kth Missing Positive Number

Given an array `arr` of positive integers sorted in a **strictly increasing order**, and an integer `k`, return the $k$th positive integer that is missing from this array.

## Example 1:

> **Input:** arr = [2,3,4,7,11], k = 5
> **Output:** 9
> **Explanation:** The missing positive integers are [1,5,6,8,9,...]. The 5th missing positive integer is 9.

## Example 2:

> **Input:** arr = [1,2,3,4], k = 2
> **Output:** 6
> **Explanation:** The missing positive integers are [5,6,7,...]. The 2nd missing positive integer is 6.

## Constraints:

- $1 \leq arr.length \leq 1000$
- $1 \leq arr[i] \leq 1000$
- $1 \leq k \leq 1000$
- `arr` is sorted in strictly increasing order.

## Follow up:

Could you solve this problem in less than $O(n)$ complexity?

## Starter Code

```dafny
predicate find_kth_positive_pre(arr: seq<int>, k: int)

predicate find_kth_positive_post(arr: seq<int>, k: int, result: int)
  requires find_kth_positive_pre(arr, k)

method find_kth_positive(arr: seq<int>, k: int) returns (result: int)
  requires find_kth_positive_pre(arr, k)
  ensures find_kth_positive_post(arr, k, result)
```

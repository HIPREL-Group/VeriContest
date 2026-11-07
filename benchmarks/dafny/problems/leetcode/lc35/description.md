# Search Insert Position

Given a sorted array of distinct integers and a target value, return the index if the target is found. If not, return the index where it would be if it were inserted in order.

You must write an algorithm with `O(log n)` runtime complexity.

## Example 1:

> **Input:** nums = [1,3,5,6], target = 5
> **Output:** 2

## Example 2:

> **Input:** nums = [1,3,5,6], target = 2
> **Output:** 1

## Example 3:

> **Input:** nums = [1,3,5,6], target = 7
> **Output:** 4

## Constraints:

- $1 <= nums.length <= 10^4$

- $-10^4 <= nums[i] <= 10^4$

- `nums` contains **distinct** values sorted in **ascending** order.

- $-10^4 <= target <= 10^4$

## Starter Code

```dafny
predicate search_insert_pre(nums: seq<int>, target: int)

predicate search_insert_post(nums: seq<int>, target: int, res: int)
  requires search_insert_pre(nums, target)

method search_insert(nums: seq<int>, target: int) returns (res: int)
  requires search_insert_pre(nums, target)
  ensures search_insert_post(nums, target, res)
```

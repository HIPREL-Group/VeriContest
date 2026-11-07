# Count Alternating Subarrays

You are given a binary array `nums`.

A subarray is called **alternating** if no two adjacent elements in the subarray have the same value.

Return the number of alternating subarrays in `nums`.

## Example 1:

> **Input:** nums = [0,1,1,1]
> **Output:** 5
> **Explanation:**
> The alternating subarrays are `[0]`, `[1]`, `[1]`, `[1]`, and `[0,1]`.

## Example 2:

> **Input:** nums = [1,0,1,0]
> **Output:** 10
> **Explanation:**
> Every subarray is alternating.

## Constraints:

- `1 <= nums.length <= 10^5`
- `nums[i]` is either `0` or `1`

## Starter Code

```dafny
predicate count_alternating_subarrays_pre(nums: seq<int>)

predicate count_alternating_subarrays_post(nums: seq<int>, result: int)
  requires count_alternating_subarrays_pre(nums)

method count_alternating_subarrays(nums: seq<int>) returns (result: int)
  requires count_alternating_subarrays_pre(nums)
  ensures count_alternating_subarrays_post(nums, result)
```

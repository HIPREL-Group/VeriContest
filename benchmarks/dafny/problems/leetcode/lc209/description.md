# 209. Minimum Size Subarray Sum

Given an array of positive integers `nums` and a positive integer `target`, return the minimal length of a contiguous subarray of which the sum is greater than or equal to `target`.

If there is no such subarray, return `0` instead.

## Example 1

- Input: `target = 7`, `nums = [2,3,1,2,4,3]`
- Output: `2`
- Explanation: The subarray `[4,3]` has the minimal length under the problem condition.

## Example 2

- Input: `target = 4`, `nums = [1,4,4]`
- Output: `1`

## Example 3

- Input: `target = 11`, `nums = [1,1,1,1,1,1,1,1]`
- Output: `0`

## Constraints

- `1 <= target <= 10^9`
- `1 <= nums.length <= 10^5`
- `1 <= nums[i] <= 10^4`

## Starter Code

```dafny
predicate min_sub_array_len_pre(target: int, nums: seq<int>)

predicate min_sub_array_len_post(target: int, nums: seq<int>, k: int)
  requires min_sub_array_len_pre(target, nums)

method min_sub_array_len(target: int, nums: seq<int>) returns (k: int)
  requires min_sub_array_len_pre(target, nums)
  ensures min_sub_array_len_post(target, nums, k)
```

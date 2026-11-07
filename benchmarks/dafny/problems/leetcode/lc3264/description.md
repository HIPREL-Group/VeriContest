# Final Array State After K Multiplication Operations I

You are given an integer array `nums`, an integer `k`, and an integer `multiplier`.

You need to perform `k` operations on `nums`. In each operation:

- Find the minimum value `x` in `nums`. If there are multiple occurrences of the minimum value, select the one that appears first.
- Replace the selected minimum value `x` with `x * multiplier`.

Return an integer array denoting the final state of `nums` after performing all `k` operations.

## Example 1:

> **Input:** nums = [2,1,3,5,6], k = 5, multiplier = 2  
> **Output:** [8,4,6,5,6]

## Example 2:

> **Input:** nums = [1,2], k = 3, multiplier = 4  
> **Output:** [16,8]

## Constraints:

- `1 <= nums.length <= 100`
- `1 <= nums[i] <= 100`
- `1 <= k <= 10`
- `1 <= multiplier <= 5`

## Starter Code

```dafny
predicate get_final_state_pre(nums: seq<int>, k: int, multiplier: int)

predicate get_final_state_post(nums: seq<int>, k: int, multiplier: int, result: seq<int>)
  requires get_final_state_pre(nums, k, multiplier)

method get_final_state(nums: seq<int>, k: int, multiplier: int) returns (result: seq<int>)
  requires get_final_state_pre(nums, k, multiplier)
  ensures get_final_state_post(nums, k, multiplier, result)
```

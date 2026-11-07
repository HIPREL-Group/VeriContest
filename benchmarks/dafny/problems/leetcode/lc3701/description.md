# Compute Alternating Sum

You are given an integer array `nums`.

The **alternating sum** of `nums` is the value obtained by adding elements at even indices and subtracting elements at odd indices. In other words, it is `nums[0] - nums[1] + nums[2] - nums[3] + ...`.

Return an integer denoting the alternating sum of `nums`.

## Example 1

> **Input:** nums = [1,3,5,7]  
> **Output:** -4  
> **Explanation:** The alternating sum is `1 - 3 + 5 - 7 = -4`.

## Example 2

> **Input:** nums = [100]  
> **Output:** 100  
> **Explanation:** The alternating sum is `100`.

## Constraints

- `1 <= nums.length <= 100`
- `1 <= nums[i] <= 100`

## Starter Code

```dafny
predicate alternating_sum_pre(nums: seq<int>)

predicate alternating_sum_post(nums: seq<int>, result: int)
  requires alternating_sum_pre(nums)

method alternating_sum(nums: seq<int>) returns (result: int)
  requires alternating_sum_pre(nums)
  ensures alternating_sum_post(nums, result)
```

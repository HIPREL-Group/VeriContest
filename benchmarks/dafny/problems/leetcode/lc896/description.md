# Monotonic Array

An array is **monotonic** if it is either monotone increasing or monotone decreasing.

An array `nums` is monotone increasing if for all `i <= j`, `nums[i] <= nums[j]`. An array `nums` is monotone decreasing if for all `i <= j`, `nums[i] >= nums[j]`.

Given an integer array `nums`, return `true` if the given array is monotonic, or `false` otherwise.

## Example 1:

> **Input:** nums = [1,2,2,3]
> **Output:** true

## Example 2:

> **Input:** nums = [6,5,4,4]
> **Output:** true

## Example 3:

> **Input:** nums = [1,3,2]
> **Output:** false

## Constraints:

- `1 <= nums.length <= 10^5`
- `-10^5 <= nums[i] <= 10^5`

## Starter Code

```dafny
predicate is_monotonic_pre(nums: seq<int>)

predicate is_monotonic_post(nums: seq<int>, result: bool)
  requires is_monotonic_pre(nums)

method is_monotonic(nums: seq<int>) returns (result: bool)
  requires is_monotonic_pre(nums)
  ensures is_monotonic_post(nums, result)
```

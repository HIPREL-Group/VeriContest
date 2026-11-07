# Move Zeroes

Given an integer array `nums`, move all `0`'s to the end of it while maintaining the relative order of the non-zero elements.

**Note** that you must do this in-place without making a copy of the array.

## Example 1:

> **Input:** nums = [0,1,0,3,12]
> **Output:** [1,3,12,0,0]

## Example 2:

> **Input:** nums = [0]
> **Output:** [0]

## Constraints:

- $1 <= nums.length <= 10^4$

- $-2^{31} <= nums[i] <= 2^{31} - 1$

## Starter Code

```dafny
predicate move_zeroes_pre(nums: seq<int>)

predicate move_zeroes_post(nums: seq<int>, result: seq<int>)
  requires move_zeroes_pre(nums)

method move_zeroes(nums: seq<int>) returns (result: seq<int>)
  requires move_zeroes_pre(nums)
  ensures move_zeroes_post(nums, result)
```

# Single Element in a Sorted Array

You are given a sorted array consisting of only integers where every element appears exactly twice, except for one element which appears exactly once.

Return *the single element that appears only once*.

## Example 1:

> **Input:** nums = [1,1,2,3,3,4,4,8,8]
> **Output:** 2

## Example 2:

> **Input:** nums = [3,3,7,7,10,11,11]
> **Output:** 10

## Constraints:

- $1 <= nums.length <= 10^5$

- $0 <= nums[i] <= 10^5$

## Starter Code

```dafny
predicate single_non_duplicate_pre(nums: seq<int>)

predicate single_non_duplicate_post(nums: seq<int>, res: int)
  requires single_non_duplicate_pre(nums)

method single_non_duplicate(nums: seq<int>) returns (res: int)
  requires single_non_duplicate_pre(nums)
  ensures single_non_duplicate_post(nums, res)
```

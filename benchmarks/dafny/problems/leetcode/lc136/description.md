# Single Number

Given a **non-empty** array of integers `nums`, every element appears *twice* except for one. Find that single one.

You must implement a solution with a linear runtime complexity and use only constant extra space.

## Example 1:

> **Input:** nums = [2,2,1]
> **Output:** 1

## Example 2:

> **Input:** nums = [4,1,2,1,2]
> **Output:** 4

## Example 3:

> **Input:** nums = [1]
> **Output:** 1

## Constraints:

- $1 <= nums.length <= 3 * 10^4$

- $-3 * 10^4 <= nums[i] <= 3 * 10^4$

- Each element in the array appears twice except for one element which appears only once.

## Starter Code

```dafny
predicate single_number_pre(nums: seq<int>)

predicate single_number_post(nums: seq<int>, res: int)
  requires single_number_pre(nums)

method single_number(nums: seq<int>) returns (res: int)
  requires single_number_pre(nums)
  ensures single_number_post(nums, res)
```

# Find All Numbers Disappeared in an Array

Given an array `nums` of `n` integers where `nums[i]` is in the range `[1, n]`, return an array of all the integers in the range `[1, n]` that do not appear in `nums`.

## Example 1:

> **Input:** nums = [4,3,2,7,8,2,3,1]
> **Output:** [5,6]

## Example 2:

> **Input:** nums = [1,1]
> **Output:** [2]


## Constraints:

- $n == nums.length$

- $1 <= n <= 10^5$

- $1 <= nums[i] <= n$

## Starter Code

```dafny
predicate find_disappeared_numbers_pre(nums: seq<int>)

predicate find_disappeared_numbers_post(nums: seq<int>, result: seq<int>)
  requires find_disappeared_numbers_pre(nums)

method find_disappeared_numbers(nums: seq<int>) returns (result: seq<int>)
  requires find_disappeared_numbers_pre(nums)
  ensures find_disappeared_numbers_post(nums, result)
```

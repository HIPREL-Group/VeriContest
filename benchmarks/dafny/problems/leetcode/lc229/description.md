# Majority Element II

Given an integer array of size `n`, find all elements that appear more than `⌊ n/3 ⌋` times.

## Example 1:

> **Input:** nums = [3,2,3]
> **Output:** [3]

## Example 2:

> **Input:** nums = [1]
> **Output:** [1]

## Example 2:

> **Input:** nums = [1,2]
> **Output:** [1,2]

## Constraints:

- $1 <= nums.length <= 5 * 10^4$

- $-10^9 <= nums[i] <= 10^9$

## Starter Code

```dafny
predicate majority_element_pre(nums: seq<int>)

predicate majority_element_post(nums: seq<int>, res: seq<int>)
  requires majority_element_pre(nums)

method majority_element(nums: seq<int>) returns (res: seq<int>)
  requires majority_element_pre(nums)
  ensures majority_element_post(nums, res)
```

# Single Number III

Given an integer array `nums`, exactly two elements appear only once and all the other elements appear exactly twice. Find the two elements that appear only once. You can return the answer in any order.

You must write an algorithm that runs in linear time and uses only constant extra space.

## Example 1:

> **Input:** nums = [1,2,1,3,2,5]
> **Output:** [3,5]
> **Explanation:** [5,3] is also a valid answer.

## Example 2:

> **Input:** nums = [-1,0]
> **Output:** [-1,0]

## Example 3:

> **Input:** nums = [0,1]
> **Output:** [1,0]

## Constraints:

- `2 <= nums.length <= 3 * 10^4`
- `-2^31 <= nums[i] <= 2^31 - 1`
- Each integer in `nums` appears twice, only two integers appear once.

## Starter Code

```dafny
predicate single_number_pre(nums: seq<int>)

predicate single_number_post(nums: seq<int>, result: seq<int>)
  requires single_number_pre(nums)

method single_number(nums: seq<int>) returns (result: seq<int>)
  requires single_number_pre(nums)
  ensures single_number_post(nums, result)
```

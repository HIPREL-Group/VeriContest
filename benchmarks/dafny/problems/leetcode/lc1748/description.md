# 1748. Sum of Unique Elements

You are given an integer array `nums`. The unique elements of an array are the elements that appear **exactly once** in the array.

Return the **sum** of all the unique elements of `nums`.

## Example 1

- **Input:** `nums = [1,2,3,2]`
- **Output:** `4`
- **Explanation:** The unique elements are `[1, 3]`, and the sum is `4`.

## Example 2

- **Input:** `nums = [1,1,1,1,1]`
- **Output:** `0`
- **Explanation:** There are no unique elements, and the sum is `0`.

## Example 3

- **Input:** `nums = [1,2,3,4,5]`
- **Output:** `15`
- **Explanation:** The unique elements are `[1, 2, 3, 4, 5]`, and the sum is `15`.

## Constraints

- $1 \leq nums.length \leq 100$
- $1 \leq nums[i] \leq 100$

## Starter Code

```dafny
predicate sum_of_unique_pre(nums: seq<int>)

predicate sum_of_unique_post(nums: seq<int>, res: int)
  requires sum_of_unique_pre(nums)

method sum_of_unique(nums: seq<int>) returns (res: int)
  requires sum_of_unique_pre(nums)
  ensures sum_of_unique_post(nums, res)
```

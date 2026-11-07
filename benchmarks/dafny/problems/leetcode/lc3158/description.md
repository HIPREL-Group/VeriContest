# Find the XOR of Numbers Which Appear Twice

You are given an array `nums` where each value appears either once or twice.

Return the bitwise `XOR` of all numbers that appear twice, or `0` if none do.

## Example 1

> **Input:** `nums = [1,2,1,3]`  
> **Output:** `1`  
> **Explanation:** Only `1` appears twice.

## Example 2

> **Input:** `nums = [1,2,3]`  
> **Output:** `0`  
> **Explanation:** No number appears twice.

## Example 3

> **Input:** `nums = [1,2,2,1]`  
> **Output:** `3`  
> **Explanation:** `1 XOR 2 = 3`.

## Constraints

- `1 <= nums.length <= 50`
- `1 <= nums[i] <= 50`
- Each number in `nums` appears either once or twice.

## Starter Code

```dafny
predicate duplicate_numbers_xor_pre(nums: seq<int>)

predicate duplicate_numbers_xor_post(nums: seq<int>, result: int)
  requires duplicate_numbers_xor_pre(nums)

method duplicate_numbers_xor(nums: seq<int>) returns (result: int)
  requires duplicate_numbers_xor_pre(nums)
  ensures duplicate_numbers_xor_post(nums, result)
```

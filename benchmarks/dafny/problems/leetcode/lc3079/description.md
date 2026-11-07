# Find the Sum of Encrypted Integers

You are given an array `nums` of positive integers.

Define `encrypt(x)` as replacing every digit of `x` with the largest digit in `x`.

For example:

- `encrypt(523) = 555`
- `encrypt(213) = 333`

Return the sum of all encrypted values.

## Example 1

> **Input:** `nums = [1,2,3]`  
> **Output:** `6`  
> **Explanation:** Encrypted values are `[1,2,3]`, so the sum is `6`.

## Example 2

> **Input:** `nums = [10,21,31]`  
> **Output:** `66`  
> **Explanation:** Encrypted values are `[11,22,33]`, so the sum is `66`.

## Constraints

- `1 <= nums.length <= 50`
- `1 <= nums[i] <= 1000`

## Starter Code

```dafny
predicate sum_of_encrypted_int_pre(nums: seq<int>)

predicate sum_of_encrypted_int_post(nums: seq<int>, result: int)
  requires sum_of_encrypted_int_pre(nums)

method sum_of_encrypted_int(nums: seq<int>) returns (result: int)
  requires sum_of_encrypted_int_pre(nums)
  ensures sum_of_encrypted_int_post(nums, result)
```

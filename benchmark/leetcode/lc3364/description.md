# Minimum Positive Sum Subarray

You are given an integer array `nums` and two integers `l` and `r`. Your task is to find the minimum sum of a subarray whose length is between `l` and `r` (inclusive) and whose sum is greater than `0`.

Return the minimum positive subarray sum. If no such subarray exists, return `-1`.

A subarray is a contiguous non-empty sequence of elements within an array.

## Example 1:

> **Input:** nums = [3, -2, 1, 4], l = 2, r = 3
> **Output:** 1
>
> **Explanation:** Valid positive subarrays with length in `[2, 3]` are `[3, -2]` (sum `1`), `[1, 4]` (sum `5`), `[3, -2, 1]` (sum `2`), and `[-2, 1, 4]` (sum `3`). The minimum positive sum is `1`.

## Example 2:

> **Input:** nums = [-2, 2, -3, 1], l = 2, r = 3
> **Output:** -1
>
> **Explanation:** No subarray with length in `[2, 3]` has a sum greater than `0`.

## Example 3:

> **Input:** nums = [1, 2, 3, 4], l = 2, r = 4
> **Output:** 3
>
> **Explanation:** The subarray `[1, 2]` has length `2` and sum `3`, which is the minimum positive sum.

## Constraints:

- `1 <= nums.length <= 100`
- `1 <= l <= r <= nums.length`
- `-1000 <= nums[i] <= 1000`

## Starter Code

```rust
impl Solution {
    pub fn minimum_sum_subarray(nums: Vec<i32>, l: i32, r: i32) -> i32 {
        
    }
}
```

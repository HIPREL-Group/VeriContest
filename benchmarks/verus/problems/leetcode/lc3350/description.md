# Adjacent Increasing Subarrays Detection II

Given an array `nums` of `n` integers, find the maximum value of `k` for which there exist two adjacent subarrays of length `k` such that both subarrays are strictly increasing. More formally, you need indices `a` and `b` with `a < b` and `b = a + k` such that:

- `nums[a..a + k - 1]` is strictly increasing.
- `nums[b..b + k - 1]` is strictly increasing.

Return the maximum possible value of `k`.

A subarray is a contiguous non-empty sequence of elements within an array.

## Example 1:

> **Input:** nums = [2,5,7,8,9,2,3,4,3,1]
> **Output:** 3
> **Explanation:** The subarray `[7, 8, 9]` starting at index 2 and the subarray `[2, 3, 4]` starting at index 5 are adjacent, strictly increasing, and both have length 3.

## Example 2:

> **Input:** nums = [1,2,3,4,4,4,4,5,6,7]
> **Output:** 2
> **Explanation:** The subarray `[1, 2]` starting at index 0 and the subarray `[3, 4]` starting at index 2 are adjacent, strictly increasing, and both have length 2.

## Constraints:

- `2 <= nums.length <= 2 * 10^5`
- `-10^9 <= nums[i] <= 10^9`

## Starter Code

```rust
impl Solution {
    pub fn max_increasing_subarrays(nums: Vec<i32>) -> i32 {
        
    }
}
```

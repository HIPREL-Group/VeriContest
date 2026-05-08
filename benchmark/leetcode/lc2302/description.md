# Count Subarrays With Score Less Than K

You are given a positive integer array `nums` and an integer `k`.

The **score** of a subarray is defined as:

- `(sum of the subarray) * (length of the subarray)`

Return the number of non-empty subarrays of `nums` whose score is strictly less than `k`.

## Example 1

- **Input:** `nums = [2,1,4,3,5]`, `k = 10`
- **Output:** `6`
- **Explanation:** The valid subarrays are `[2]`, `[1]`, `[4]`, `[3]`, `[5]`, and `[2,1]`.

## Example 2

- **Input:** `nums = [1,1,1]`, `k = 5`
- **Output:** `5`
- **Explanation:** All subarrays except `[1,1,1]` have score less than `5`.

## Constraints

- `1 <= nums.length <= 10^5`
- `1 <= nums[i] <= 10^5`
- `1 <= k <= 10^15`

## Starter Code

```rust
impl Solution {
    pub fn count_subarrays(nums: Vec<i32>, k: i64) -> i64 {
        
    }
}
```

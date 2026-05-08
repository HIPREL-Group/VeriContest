# Adjacent Increasing Subarrays Detection I

Given an array `nums` of `n` integers and an integer `k`, determine whether there exist two adjacent subarrays of length `k` such that both subarrays are strictly increasing.

More formally, check if there is an index `a` such that:

- `nums[a..a + k - 1]` is strictly increasing.
- `nums[a + k..a + 2 * k - 1]` is strictly increasing.

Return `true` if such subarrays exist, and `false` otherwise.

## Example 1:

> **Input:** nums = [2,5,7,8,9,2,3,4,3,1], k = 3
> **Output:** true
> **Explanation:** `[7, 8, 9]` and `[2, 3, 4]` are adjacent strictly increasing subarrays of length 3.

## Example 2:

> **Input:** nums = [1,2,3,4,4,4,4,5,6,7], k = 5
> **Output:** false

## Constraints:

- `2 <= nums.length <= 100`
- `1 < 2 * k <= nums.length`
- `-1000 <= nums[i] <= 1000`

## Starter Code

```rust
impl Solution {
    pub fn has_increasing_subarrays(nums: Vec<i32>, k: i32) -> bool {
        
    }
}
```

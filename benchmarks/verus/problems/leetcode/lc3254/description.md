# Find the Power of K-Size Subarrays I

You are given an array of integers `nums` of length `n` and a positive integer `k`.

The **power** of an array is defined as:

- Its maximum element if all of its elements are consecutive and sorted in ascending order.
- `-1` otherwise.

You need to find the power of all subarrays of `nums` of size `k`.

Return an integer array `results` of size `n - k + 1`, where `results[i]` is the power of `nums[i..(i + k - 1)]`.

## Example 1:

> **Input:** nums = [1,2,3,4,3,2,5], k = 3
> **Output:** [3,4,-1,-1,-1]
> **Explanation:**
> There are 5 subarrays of `nums` of size 3:
> - `[1,2,3]` has power 3.
> - `[2,3,4]` has power 4.
> - `[3,4,3]` is not consecutive.
> - `[4,3,2]` is not sorted in ascending order.
> - `[3,2,5]` is not consecutive.

## Example 2:

> **Input:** nums = [2,2,2,2,2], k = 4
> **Output:** [-1,-1]

## Example 3:

> **Input:** nums = [3,2,3,2,3,2], k = 2
> **Output:** [-1,3,-1,3,-1]

## Constraints:

- `1 <= n == nums.length <= 500`
- `1 <= nums[i] <= 10^5`
- `1 <= k <= n`

## Starter Code

```rust
impl Solution {
    pub fn results_array(nums: Vec<i32>, k: i32) -> Vec<i32> {
        
    }
}
```

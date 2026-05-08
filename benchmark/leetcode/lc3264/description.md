# Final Array State After K Multiplication Operations I

You are given an integer array `nums`, an integer `k`, and an integer `multiplier`.

You need to perform `k` operations on `nums`. In each operation:

- Find the minimum value `x` in `nums`. If there are multiple occurrences of the minimum value, select the one that appears first.
- Replace the selected minimum value `x` with `x * multiplier`.

Return an integer array denoting the final state of `nums` after performing all `k` operations.

## Example 1:

> **Input:** nums = [2,1,3,5,6], k = 5, multiplier = 2  
> **Output:** [8,4,6,5,6]

## Example 2:

> **Input:** nums = [1,2], k = 3, multiplier = 4  
> **Output:** [16,8]

## Constraints:

- `1 <= nums.length <= 100`
- `1 <= nums[i] <= 100`
- `1 <= k <= 10`
- `1 <= multiplier <= 5`

## Starter Code

```rust
impl Solution {
    pub fn get_final_state(nums: Vec<i32>, k: i32, multiplier: i32) -> Vec<i32> {
        
    }
}
```

# Minimum Operations to Exceed Threshold Value II

You are given a 0-indexed integer array `nums`, and an integer `k`.

You are allowed to perform operations on `nums`. In one operation, you can:

- Select the two smallest integers `x` and `y` in `nums`.
- Remove `x` and `y` from `nums`.
- Insert `min(x, y) * 2 + max(x, y)` into `nums`.

You can only apply an operation when `nums` has at least two elements.

Return the minimum number of operations needed so that all elements of `nums` are greater than or equal to `k`.

## Example 1:

> **Input:** nums = [2,11,10,1,3], k = 10
> **Output:** 2
> **Explanation:**
> After the first operation, nums becomes [4,11,10,3].
> After the second operation, nums becomes [10,11,10].
> Now all elements are greater than or equal to 10.

## Example 2:

> **Input:** nums = [1,1,2,4,9], k = 20
> **Output:** 4
> **Explanation:**
> After one operation, nums becomes [2,4,9,3].
> After two operations, nums becomes [7,4,9].
> After three operations, nums becomes [15,9].
> After four operations, nums becomes [33].
> Now all elements are greater than or equal to 20.

## Constraints:

- `2 <= nums.length <= 2 * 10^5`
- `1 <= nums[i], k <= 10^9`
- The input is generated such that an answer always exists.

## Starter Code

```rust
impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        
    }
}
```

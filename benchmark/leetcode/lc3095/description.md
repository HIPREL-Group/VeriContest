# Shortest Subarray With OR at Least K I

You are given an array `nums` of non-negative integers and an integer `k`.

A subarray is called special if the bitwise OR of all its elements is at least `k`.

Return the length of the shortest non-empty special subarray of `nums`, or `-1` if no such subarray exists.

## Example 1

> **Input:** `nums = [1,2,3]`, `k = 2`  
> **Output:** `1`  
> **Explanation:** `[3]` has OR `3`, so the answer is `1`. (`[2]` also works.)

## Example 2

> **Input:** `nums = [2,1,8]`, `k = 10`  
> **Output:** `3`  
> **Explanation:** `[2,1,8]` has OR `11`, so the answer is `3`.

## Example 3

> **Input:** `nums = [1,2]`, `k = 0`  
> **Output:** `1`  
> **Explanation:** `[1]` has OR `1`, so the answer is `1`.

## Constraints

- `1 <= nums.length <= 50`
- `0 <= nums[i] <= 50`
- `0 <= k < 64`

## Starter Code

```rust
impl Solution {
    pub fn minimum_subarray_length(nums: Vec<i32>, k: i32) -> i32 {
        
    }
}
```

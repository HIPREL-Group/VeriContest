# Minimize Length of Array Using Operations

You are given a **0-indexed** integer array `nums` containing **positive** integers.

Your task is to minimize the length of `nums` by performing the following operations any number of times (including zero):

- Select two distinct indices `i` and `j` from `nums`, such that `nums[i] > 0` and `nums[j] > 0`.

- Insert the result of `nums[i] % nums[j]` at the end of `nums`.

- Delete the elements at indices `i` and `j` from `nums`.

Return the minimum possible length of `nums` after performing the operations.

## Example 1:

> **Input:** nums = [1,4,3,1]  
> **Output:** 1

## Example 2:

> **Input:** nums = [5,5,5,10,5]  
> **Output:** 2

## Example 3:

> **Input:** nums = [2,3,4]  
> **Output:** 1

## Constraints:

- `1 <= nums.length <= 10^5`
- `1 <= nums[i] <= 10^9`

## Starter Code

```rust
impl Solution {
    pub fn minimum_array_length(nums: Vec<i32>) -> i32 {
        
    }
}
```

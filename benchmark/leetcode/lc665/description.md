# Non-decreasing Array

Given an array `nums` with `n` integers, check if it could become non-decreasing by modifying **at most one element**.

We define an array as non-decreasing if `nums[i] <= nums[i + 1]` holds for every `i` (0-indexed) such that `0 <= i <= n - 2`.

## Example 1:

> **Input:** nums = [4,2,3]
> **Output:** true
> **Explanation:** You could modify the first 4 to 1 to get a non-decreasing array.

## Example 2:

> **Input:** nums = [4,2,1]
> **Output:** false
> **Explanation:** You cannot get a non-decreasing array by modifying at most one element.

## Constraints:

- $n == \text{nums.length}$
- $1 \leq n \leq 10^4$
- $-10^8 \leq \text{nums}[i] \leq 10^8$

## Starter Code

```rust
impl Solution {
    pub fn check_possibility(nums: Vec<i32>) -> bool {
        
    }
}
```

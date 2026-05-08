# Minimum Elements to Add to Form a Given Sum

You are given an integer array `nums` and two integers `limit` and `goal`. The array `nums` has an interesting property that `abs(nums[i]) <= limit`.

Return the minimum number of elements you need to add to make the sum of the array equal to `goal`. The array must maintain its property that `abs(nums[i]) <= limit`.

Note that `abs(x)` equals `x` if `x >= 0`, and `-x` otherwise.

## Example 1:

> **Input:** nums = [1,-1,1], limit = 3, goal = -4
> **Output:** 2
> **Explanation:** You can add -2 and -3, then the sum of the array will be 1 - 1 + 1 - 2 - 3 = -4.

## Example 2:

> **Input:** nums = [1,-10,9,1], limit = 100, goal = 0
> **Output:** 1

## Constraints:

- $1 \leq \text{nums.length} \leq 10^5$
- $1 \leq \text{limit} \leq 10^6$
- $-\text{limit} \leq \text{nums[i]} \leq \text{limit}$
- $-10^9 \leq \text{goal} \leq 10^9$

## Starter Code

```rust
impl Solution {
    pub fn min_elements(nums: Vec<i32>, limit: i32, goal: i32) -> i32 {
        
    }
}
```

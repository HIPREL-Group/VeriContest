# Longest Continuous Subarray With Absolute Diff Less Than or Equal to Limit

Given an array of integers `nums` and an integer `limit`, return the size of the longest non-empty subarray such that the absolute difference between any two elements in the subarray is less than or equal to `limit`.

## Example 1:

> **Input:** nums = [8,2,4,7], limit = 4
> **Output:** 2
> **Explanation:** The longest valid subarrays are [2,4] and [4,7], both of length 2.

## Example 2:

> **Input:** nums = [10,1,2,4,7,2], limit = 5
> **Output:** 4
> **Explanation:** The subarray [2,4,7,2] is the longest valid subarray since $|2 - 7| = 5$.

## Example 3:

> **Input:** nums = [4,2,2,2,4,4,2,2], limit = 0
> **Output:** 3

## Constraints:

- $1 <= \text{nums.length} <= 10^5$
- $1 <= \text{nums}[i] <= 10^9$
- $0 <= \text{limit} <= 10^9$

## Starter Code

```rust
impl Solution {
    pub fn longest_subarray(nums: Vec<i32>, limit: i32) -> i32 {
        
    }
}
```

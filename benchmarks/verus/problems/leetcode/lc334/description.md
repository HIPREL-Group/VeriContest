# Increasing Triplet Subsequence

Given an integer array `nums`, return `true` if there exists a triple of indices `(i, j, k)` such that `i < j < k` and `nums[i] < nums[j] < nums[k]`. If no such indices exists, return `false`.

## Example 1:
> **Input:** nums = [1,2,3,4,5]
> **Output:** true
> **Explanation:**
> Any triplet where i < j < k is valid.

## Example 2:
> **Input:** nums = [5,4,3,2,1]
> **Output:** false
> **Explanation:**
> No triplet exists.

## Example 3:
> **Input:** nums = [2,1,5,0,4,6]
> **Output:** true
> **Explanation:**
> One of the valid triplets is (1, 4, 5), because nums[1] == 1 < nums[4] == 4 < nums[5] == 6.

## Constraints:

- $1 \leq nums.length \leq 5 \times 10^5$

- $-2^{31} \leq nums[i] \leq 2^{31} - 1$

## Follow up:

Could you implement a solution that runs in `O(n)` time complexity and `O(1)` space complexity?

## Starter Code

```rust
impl Solution {
    pub fn increasing_triplet(nums: Vec<i32>) -> bool {
        
    }
}
```

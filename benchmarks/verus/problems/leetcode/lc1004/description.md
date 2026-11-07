# Max Consecutive Ones III

Given a binary array `nums` and an integer `k`, return the maximum number of consecutive `1`'s in the array if you can flip at most `k` `0`'s.

## Example 1:

> **Input:** nums = [1,1,1,0,0,0,1,1,1,1,0], k = 2
> **Output:** 6
> **Explanation:** The underlined subarray `[1,1,1,0,0,1,1,1,1,1,1]` (with 2 zeros flipped) has the maximum length of 6.

## Example 2:

> **Input:** nums = [0,0,1,1,0,0,1,1,1,0,1,1,0,0,0,1,1,1,1], k = 3
> **Output:** 10
> **Explanation:** The underlined subarray `[1,1,1,1,1,1,1,1,1,1]` (with 3 zeros flipped) has the maximum length of 10.

## Constraints:

- $1 \leq$ `nums.length` $\leq 10^5$
- `nums[i]` is either `0` or `1`.
- $0 \leq$ `k` $\leq$ `nums.length`

## Starter Code

```rust
impl Solution {
    pub fn longest_ones(nums: Vec<i32>, k: i32) -> i32 {
        
    }
}
```

# Maximize the Topmost Element After K Moves

You are given a 0-indexed integer array `nums` representing a pile, where `nums[0]` is the topmost element.

In one move, you can do either of the following:

- If the pile is not empty, remove the topmost element.

- If there is at least one removed element, add any one removed element back onto the pile. That element becomes the new top.

You are also given an integer `k`, the total number of moves.

Return the maximum possible topmost element after exactly `k` moves. If it is impossible to end with a non-empty pile, return `-1`.

## Example 1:

> **Input:** nums = [5,2,2,4,0,6], k = 4
> **Output:** 5
> **Explanation:**
> One valid sequence is:
> - Remove 5 → [2,2,4,0,6]
> - Remove 2 → [2,4,0,6]
> - Remove 2 → [4,0,6]
> - Add back 5 → [5,4,0,6]
> This achieves the largest possible top value.

## Example 2:

> **Input:** nums = [2], k = 1
> **Output:** -1
> **Explanation:**
> After one move the only action is removing 2, leaving the pile empty.

## Constraints:

- $1 \leq nums.length \leq 10^5$

- $0 \leq nums[i], k \leq 10^9$

## Starter Code

```rust
impl Solution {
    pub fn maximum_top(nums: Vec<i32>, k: i32) -> i32 {
        
    }
}
```

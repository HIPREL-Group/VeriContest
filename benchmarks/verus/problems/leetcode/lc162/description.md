# Find Peak Element

A peak element is an element that is strictly greater than its neighbors.

Given a **0-indexed** integer array `nums`, find a peak element, and return its index. If the array contains multiple peaks, return the index to **any** of the peaks.

You may imagine that `nums[-1] = nums[n] = -∞`. In other words, an element is always considered to be strictly greater than a neighbor that is outside the array.

## Example 1:

> **Input:** nums = [1,2,3,1]
> **Output:** 2
> **Explanation:** `nums[2]` is a peak element because `nums[2] = 3` is strictly greater than both its neighbors `nums[1] = 2` and `nums[3] = 1`.

## Example 2:

> **Input:** nums = [1,2,1,3,5,6,4]
> **Output:** 5
> **Explanation:** Your function can return either index 1 where the peak element is 2, or index 5 where the peak element is 6.

You must write an algorithm that runs in $O(\log n)$ time.

## Constraints:

- $1 \leq nums.length \leq 1000$

- $-2^{31} \leq nums[i] \leq 2^{31} - 1$

- `nums[i] != nums[i + 1]` for all valid `i`

## Starter Code

```rust
impl Solution {
    pub fn find_peak_element(nums: Vec<i32>) -> i32 {
        
    }
}
```

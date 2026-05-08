# Special Array I

An array is considered **special** if the parity of every pair of adjacent elements is different. In other words, one element in each pair must be even, and the other must be odd.

You are given an array of integers `nums`. Return `true` if `nums` is a special array. Otherwise, return `false`.

## Example 1:

> **Input:** nums = [1]
> **Output:** true
> **Explanation:** There is only one element, so the array is special.

## Example 2:

> **Input:** nums = [2,1,4]
> **Output:** true
> **Explanation:** The pairs `(2,1)` and `(1,4)` have different parity.

## Example 3:

> **Input:** nums = [4,3,1,6]
> **Output:** false
> **Explanation:** `nums[1]` and `nums[2]` are both odd.

## Constraints:

- `1 <= nums.length <= 100`
- `1 <= nums[i] <= 100`

## Starter Code

```rust
impl Solution {
    pub fn is_array_special(nums: Vec<i32>) -> bool {
        
    }
}
```

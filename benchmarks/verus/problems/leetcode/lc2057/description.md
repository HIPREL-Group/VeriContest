# Smallest Index With Equal Value

Given a 0-indexed integer array `nums`, return the smallest index `i` such that `i mod 10 == nums[i]`, or `-1` if no such index exists.

`x mod y` denotes the remainder when `x` is divided by `y`.

## Example 1:

> **Input:** nums = [0,1,2]
> **Output:** 0
> **Explanation:** Every index satisfies `i mod 10 == nums[i]`, so the smallest valid index is 0.

## Example 2:

> **Input:** nums = [4,3,2,1]
> **Output:** 2
> **Explanation:** Index 2 is the only index such that `i mod 10 == nums[i]`.

## Example 3:

> **Input:** nums = [1,2,3,4,5,6,7,8,9,0]
> **Output:** -1
> **Explanation:** No index satisfies `i mod 10 == nums[i]`.

## Constraints:

- `1 <= nums.length <= 100`
- `0 <= nums[i] <= 9`

## Starter Code

```rust
impl Solution {
    pub fn smallest_equal(nums: Vec<i32>) -> i32 {
        
    }
}
```

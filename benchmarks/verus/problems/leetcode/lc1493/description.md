# Longest Subarray of 1's After Deleting One Element

Given a binary array `nums`, you should delete one element from it.

Return the size of the longest non-empty subarray containing only `1`'s in the resulting array. Return `0` if there is no such subarray.

## Example 1:

> **Input:** nums = [1,1,0,1]
> **Output:** 3
> **Explanation:** After deleting the number at position 2, [1,1,1] contains 3 numbers with value 1.

## Example 2:

> **Input:** nums = [0,1,1,1,0,1,1,0,1]
> **Output:** 5
> **Explanation:** After deleting the number at position 4, [0,1,1,1,1,1,0,1] has a longest subarray of 1's equal to [1,1,1,1,1].

## Example 3:

> **Input:** nums = [1,1,1]
> **Output:** 2
> **Explanation:** You must delete one element.

## Constraints:

- `1 <= nums.length <= 10^5`
- `nums[i]` is either `0` or `1`.

## Starter Code

```rust
impl Solution {
    pub fn longest_subarray(nums: Vec<i32>) -> i32 {
        
    }
}
```

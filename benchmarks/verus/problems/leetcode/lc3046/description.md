# Split the Array

You are given an integer array `nums` of even length. You have to split the array into two parts `nums1` and `nums2` such that:

- `nums1.length == nums2.length == nums.length / 2`
- `nums1` contains distinct elements
- `nums2` contains distinct elements

Return `true` if it is possible to split the array, and `false` otherwise.

## Example 1:

> **Input:** nums = [1,1,2,2,3,4]
> **Output:** true
> **Explanation:** One possible split is nums1 = [1,2,3] and nums2 = [1,2,4].

## Example 2:

> **Input:** nums = [1,1,1,1]
> **Output:** false
> **Explanation:** The only possible split is nums1 = [1,1] and nums2 = [1,1]. Neither part contains distinct elements.

## Constraints:

- $1 <= nums.length <= 100$
- $nums.length \% 2 == 0$
- $1 <= nums[i] <= 100$

## Starter Code

```rust
impl Solution {
    pub fn is_possible_to_split(nums: Vec<i32>) -> bool {
        
    }
}
```

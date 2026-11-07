# Minimum Pair Removal to Sort Array I

Given an array `nums`, you can perform the following operation any number of times:

- Select the adjacent pair with the minimum sum in `nums`. If multiple such pairs exist, choose the leftmost one.
- Replace the pair with their sum.

Return the minimum number of operations needed to make the array non-decreasing.

An array is non-decreasing if each element is greater than or equal to its previous element.

## Example 1:

> **Input:** nums = [5,2,3,1]
> **Output:** 2
>
> **Explanation:**
> - The pair (3,1) has the minimum sum of 4. After replacement, nums = [5,2,4].
> - The pair (2,4) has the minimum sum of 6. After replacement, nums = [5,6].
> The array becomes non-decreasing in two operations.

## Example 2:

> **Input:** nums = [1,2,2]
> **Output:** 0
>
> **Explanation:**
> The array is already non-decreasing.

## Constraints:

- `1 <= nums.length <= 50`
- `-1000 <= nums[i] <= 1000`

## Starter Code

```rust
impl Solution {
    pub fn minimum_pair_removal(nums: Vec<i32>) -> i32 {
        
    }
}
```

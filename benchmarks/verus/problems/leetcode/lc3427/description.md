# Sum of Variable Length Subarrays

You are given an integer array `nums` of size `n`. For each index `i` (`0 <= i < n`), define a subarray `nums[start..i]`, where `start = max(0, i - nums[i])`.

Return the total sum of all elements from the subarray defined for each index in the array.

## Example 1:

> **Input:** nums = [2,3,1]
> **Output:** 11
>
> **Explanation:**
> - `i = 0`: subarray `nums[0..0] = [2]`, sum = 2
> - `i = 1`: subarray `nums[0..1] = [2,3]`, sum = 5
> - `i = 2`: subarray `nums[1..2] = [3,1]`, sum = 4
> - Total = 2 + 5 + 4 = 11

## Example 2:

> **Input:** nums = [3,1,1,2]
> **Output:** 13
>
> **Explanation:**
> - `i = 0`: subarray `nums[0..0] = [3]`, sum = 3
> - `i = 1`: subarray `nums[0..1] = [3,1]`, sum = 4
> - `i = 2`: subarray `nums[1..2] = [1,1]`, sum = 2
> - `i = 3`: subarray `nums[1..3] = [1,1,2]`, sum = 4
> - Total = 3 + 4 + 2 + 4 = 13

## Constraints:

- `1 <= n == nums.length <= 100`
- `1 <= nums[i] <= 1000`

## Starter Code

```rust
impl Solution {
    pub fn subarray_sum(nums: Vec<i32>) -> i32 {
        
    }
}
```

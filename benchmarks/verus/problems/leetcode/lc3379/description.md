# Transformed Array

You are given an integer array `nums` that represents a circular array. Your task is to create a new array `result` of the same size.

For each index `i` (`0 <= i < nums.length`):

- If `nums[i] > 0`, start at index `i` and move `nums[i]` steps to the right in the circular array. Set `result[i]` to the value at the index where you land.
- If `nums[i] < 0`, start at index `i` and move `abs(nums[i])` steps to the left in the circular array. Set `result[i]` to the value at the index where you land.
- If `nums[i] == 0`, set `result[i]` to `nums[i]`.

Return the new array `result`.

Since `nums` is circular, moving past the last element wraps around to the beginning, and moving before the first element wraps back to the end.

## Example 1:

> **Input:** nums = [3,-2,1,1]
> **Output:** [1,1,1,3]
>
> **Explanation:**
> - For `nums[0] = 3`, moving 3 steps to the right lands at index 3, so `result[0] = 1`.
> - For `nums[1] = -2`, moving 2 steps to the left lands at index 3, so `result[1] = 1`.
> - For `nums[2] = 1`, moving 1 step to the right lands at index 3, so `result[2] = 1`.
> - For `nums[3] = 1`, moving 1 step to the right lands at index 0, so `result[3] = 3`.

## Example 2:

> **Input:** nums = [-1,4,-1]
> **Output:** [-1,-1,4]
>
> **Explanation:**
> - For `nums[0] = -1`, moving 1 step to the left lands at index 2, so `result[0] = -1`.
> - For `nums[1] = 4`, moving 4 steps to the right lands at index 2, so `result[1] = -1`.
> - For `nums[2] = -1`, moving 1 step to the left lands at index 1, so `result[2] = 4`.

## Constraints:

- `1 <= nums.length <= 100`
- `-100 <= nums[i] <= 100`

## Starter Code

```rust
impl Solution {
    pub fn construct_transformed_array(nums: Vec<i32>) -> Vec<i32> {
        
    }
}
```

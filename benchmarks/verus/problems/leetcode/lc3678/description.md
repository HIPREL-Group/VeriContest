# Smallest Absent Positive Greater Than Average

You are given an integer array `nums`.

Return the **smallest absent positive** integer in `nums` such that it is **strictly greater** than the average of all elements in `nums`.

The average of an array is defined as the sum of all its elements divided by the number of elements.

## Example 1

> **Input:** `nums = [3,5]`
> **Output:** `6`

The average is `(3 + 5) / 2 = 4`. The smallest absent positive integer greater than `4` is `6`.

## Example 2

> **Input:** `nums = [-1,1,2]`
> **Output:** `3`

The average is `(-1 + 1 + 2) / 3 = 2 / 3`. The smallest absent positive integer greater than `2 / 3` is `3`.

## Example 3

> **Input:** `nums = [4,-1]`
> **Output:** `2`

The average is `(4 + (-1)) / 2 = 3 / 2`. The smallest absent positive integer greater than `3 / 2` is `2`.

## Constraints

- `1 <= nums.length <= 100`
- `-100 <= nums[i] <= 100`

## Starter Code

```rust
impl Solution {
    pub fn smallest_absent(nums: Vec<i32>) -> i32 {
        
    }
}
```

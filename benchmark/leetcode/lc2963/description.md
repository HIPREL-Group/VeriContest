# Count the Number of Good Partitions

You are given an integer array `nums`.

A partition of `nums` into one or more contiguous subarrays is called **good** if every distinct value of `nums` appears in exactly one subarray of the partition. Equivalently, no value may appear in two different parts.

Return the number of good partitions of `nums`. Since the answer can be large, return it modulo `1_000_000_007`.

## Example 1

- **Input:** `nums = [1,2,3,4]`
- **Output:** `8`
- **Explanation:** Every cut position is valid, so there are `2^(4-1) = 8` good partitions.

## Example 2

- **Input:** `nums = [1,1,1,1]`
- **Output:** `1`
- **Explanation:** All occurrences of `1` must stay in the same part.

## Example 3

- **Input:** `nums = [1,2,1,3]`
- **Output:** `2`
- **Explanation:** The value `1` forces the prefix `[1,2,1]` to stay together, and the last value `3` forms the second block.

## Constraints

- `1 <= nums.length <= 10^5`
- `1 <= nums[i] <= 10^9`

## Starter Code

```rust
impl Solution {
    pub fn number_of_good_partitions(nums: Vec<i32>) -> i32 {
        
    }
}
```

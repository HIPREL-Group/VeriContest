# Sort Integers by Binary Reflection

You are given an integer array `nums`.

The **binary reflection** of a **positive** integer is the number obtained by reversing the order of its binary digits (ignoring any leading zeros) and interpreting the resulting binary number as a decimal integer.

Sort the array in **ascending** order based on the binary reflection of each element. If two different numbers have the same binary reflection, the **smaller** original number should appear first.

Return the resulting sorted array.

## Example 1:

> **Input:** nums = [4,5,4]
> **Output:** [4,4,5]

**Explanation:**

- 4 -> (binary) `100` -> (reversed) `001` -> 1
- 5 -> (binary) `101` -> (reversed) `101` -> 5
- 4 -> (binary) `100` -> (reversed) `001` -> 1

Sorting by reflected values gives `[4, 4, 5]`.

## Example 2:

> **Input:** nums = [3,6,5,8]
> **Output:** [8,3,6,5]

**Explanation:**

- 3 -> (binary) `11` -> (reversed) `11` -> 3
- 6 -> (binary) `110` -> (reversed) `011` -> 3
- 5 -> (binary) `101` -> (reversed) `101` -> 5
- 8 -> (binary) `1000` -> (reversed) `0001` -> 1

Sorting by reflected values gives `[8, 3, 6, 5]`.

3 and 6 have the same reflection, so they are arranged in increasing order of original value.

## Constraints:

- `1 <= nums.length <= 100`
- `1 <= nums[i] <= 10^9`

## Starter Code

```rust
impl Solution {
    pub fn sort_by_reflection(nums: Vec<i32>) -> Vec<i32> {
        
    }
}
```

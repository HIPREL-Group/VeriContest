# Find if Array Can Be Sorted

You are given a **0-indexed** array of **positive** integers `nums`.

In one operation, you can swap any two adjacent elements if they have the same number of set bits. You are allowed to do this operation any number of times (including zero).

Return `true` if you can sort the array in ascending order; otherwise, return `false`.

## Example 1:

> **Input:** nums = [8,4,2,30,15]  
> **Output:** true  
> **Explanation:**  
> The numbers 2, 4, and 8 each have one set bit.  
> The numbers 15 and 30 each have four set bits.  
> We can sort using valid adjacent swaps and obtain `[2,4,8,15,30]`.

## Example 2:

> **Input:** nums = [1,2,3,4,5]  
> **Output:** true

## Example 3:

> **Input:** nums = [3,16,8,4,2]  
> **Output:** false

## Constraints:

- `1 <= nums.length <= 100`
- `1 <= nums[i] <= 2^8`

## Starter Code

```rust
impl Solution {
    pub fn can_sort_array(nums: Vec<i32>) -> bool {
        
    }
}
```

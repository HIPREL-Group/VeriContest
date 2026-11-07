# Removing Minimum and Maximum From Array

You are given a `0`-indexed array of distinct integers `nums`.

There is an element in `nums` that has the lowest value and an element that has the highest value. We call them the minimum and maximum respectively. Your goal is to remove both these elements from the array.

A deletion is defined as either removing an element from the front of the array or removing an element from the back of the array.

Return the minimum number of deletions it would take to remove both the minimum and maximum element from the array.

## Example 1:

> **Input:** nums = [2,10,7,5,4,1,8,6]
> **Output:** 5
> **Explanation:**  
> The minimum element is `nums[5] = 1`.  
> The maximum element is `nums[1] = 10`.  
> Remove 2 elements from the front and 3 from the back for a total of 5 deletions.

## Example 2:

> **Input:** nums = [0,-4,19,1,8,-2,-3,5]
> **Output:** 3
> **Explanation:**  
> The minimum element is `nums[1] = -4`.  
> The maximum element is `nums[2] = 19`.  
> Removing 3 elements from the front removes both.

## Example 3:

> **Input:** nums = [101]
> **Output:** 1
> **Explanation:**  
> The only element is both minimum and maximum, so one deletion is enough.

## Constraints:

- `1 <= nums.length <= 10^5`
- `-10^5 <= nums[i] <= 10^5`
- All integers in `nums` are distinct.

## Starter Code

```rust
impl Solution {
    pub fn minimum_deletions(nums: Vec<i32>) -> i32 {
        
    }
}
```

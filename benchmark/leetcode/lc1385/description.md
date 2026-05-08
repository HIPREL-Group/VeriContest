# Find the Distance Value Between Two Arrays

Given two integer arrays `arr1` and `arr2`, and the integer `d`, *return the distance value between the two arrays*.

The distance value is defined as the number of elements `arr1[i]` such that there is not any element `arr2[j]` where `|arr1[i]-arr2[j]| <= d`.

## Example 1:

> **Input:** arr1 = [4,5,8], arr2 = [10,9,1,8], d = 2  
> **Output:** 2  
> **Explanation:**  
> For arr1[0] = 4, all distances are greater than 2.  
> For arr1[1] = 5, all distances are greater than 2.  
> For arr1[2] = 8, there exists arr2[j] = 10 with |8 - 10| = 2 <= 2.

## Example 2:

> **Input:** arr1 = [1,4,2,3], arr2 = [-4,-3,6,10,20,30], d = 3  
> **Output:** 2

## Example 3:

> **Input:** arr1 = [2,1,100,3], arr2 = [-5,-2,10,-3,7], d = 6  
> **Output:** 1

## Constraints:

- `1 <= arr1.length, arr2.length <= 500`
- `-1000 <= arr1[i], arr2[j] <= 1000`
- `0 <= d <= 100`

## Starter Code

```rust
impl Solution {
    pub fn find_the_distance_value(arr1: Vec<i32>, arr2: Vec<i32>, d: i32) -> i32 {
        
    }
}
```

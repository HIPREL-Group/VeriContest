# Create Target Array in the Given Order

Given two arrays of integers `nums` and `index`. Your task is to create *target* array under the following rules:

- Initially *target* array is empty.
- From left to right read `nums[i]` and `index[i]`, insert at index `index[i]` the value `nums[i]` in *target* array.
- Repeat the previous step until there are no elements to read in `nums` and `index`.

Return the *target* array.

It is guaranteed that the insertion operations will be valid.

## Example 1:

> **Input:** nums = [0,1,2,3,4], index = [0,1,2,2,1]
> **Output:** [0,4,1,3,2]

## Example 2:

> **Input:** nums = [1,2,3,4,0], index = [0,1,2,3,0]
> **Output:** [0,1,2,3,4]

## Example 3:

> **Input:** nums = [1], index = [0]
> **Output:** [1]

## Constraints:

- $1 \leq nums.length, index.length \leq 100$
- $nums.length == index.length$
- $0 \leq nums[i] \leq 100$
- $0 \leq index[i] \leq i$

## Starter Code

```rust
impl Solution {
    pub fn create_target_array(nums: Vec<i32>, index: Vec<i32>) -> Vec<i32> {
        
    }
}
```

# Minimum Capacity Box

You are given an integer array `capacity`, where `capacity[i]` represents the capacity of the `i`th box, and an integer `itemSize` representing the size of an item.

The `i`th box can store the item if `capacity[i] >= itemSize`.

Return an integer denoting the index of the box with the **minimum** capacity that can store the item. If multiple such boxes exist, return the **smallest index**.

If no box can store the item, return `-1`.

## Example 1:

> **Input:** capacity = [1,5,3,7], itemSize = 3  
> **Output:** 2

## Example 2:

> **Input:** capacity = [3,5,4,3], itemSize = 2  
> **Output:** 0

## Example 3:

> **Input:** capacity = [4], itemSize = 5  
> **Output:** -1

## Constraints:

- $1 <= capacity.length <= 100$
- $1 <= capacity[i] <= 100$
- $1 <= itemSize <= 100$

## Starter Code

```rust
impl Solution {
    pub fn minimum_index(capacity: Vec<i32>, item_size: i32) -> i32 {
        
    }
}
```

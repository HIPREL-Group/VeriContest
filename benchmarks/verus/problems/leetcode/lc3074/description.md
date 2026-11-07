# Apple Redistribution into Boxes

You are given an array `apple` of size `n` and an array `capacity` of size `m`.

There are `n` packs where the `i`th pack contains `apple[i]` apples. There are `m` boxes, and the `i`th box has capacity `capacity[i]`.

Return the minimum number of boxes needed to redistribute all apples.

Apples from the same pack may be split across multiple boxes.

## Example 1

> **Input:** `apple = [1,3,2]`, `capacity = [4,3,1,5,2]`  
> **Output:** `2`  
> **Explanation:** Choosing boxes with capacities `5` and `4` is enough.

## Example 2

> **Input:** `apple = [5,5,5]`, `capacity = [2,4,2,7]`  
> **Output:** `4`  
> **Explanation:** All boxes are needed.

## Constraints

- `1 <= n == apple.length <= 50`
- `1 <= m == capacity.length <= 50`
- `1 <= apple[i], capacity[i] <= 50`
- The input is generated such that redistribution is possible.

## Starter Code

```rust
impl Solution {
    pub fn minimum_boxes(apple: Vec<i32>, capacity: Vec<i32>) -> i32 {
        
    }
}
```

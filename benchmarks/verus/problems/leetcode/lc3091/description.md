# Apply Operations to Make Sum of Array Greater Than or Equal to k

You are given a positive integer `k`. Initially, you have an array `nums = [1]`.

You can apply the following operations any number of times:

- Choose any element in the array and increase it by `1`.
- Duplicate any element in the array and append the duplicate to the end of the array.

Return the minimum number of operations required so that the sum of elements in the final array is greater than or equal to `k`.

## Example 1:

> **Input:** k = 11
> **Output:** 5
> **Explanation:** Increase `1` three times to get `[4]`, then duplicate `4` two times to get `[4,4,4]` with sum `12`.

## Example 2:

> **Input:** k = 1
> **Output:** 0
> **Explanation:** The initial array already has sum `1`.

## Constraints:

- `1 <= k <= 10^5`

## Starter Code

```rust
impl Solution {
    pub fn min_operations(k: i32) -> i32 {
        
    }
}
```

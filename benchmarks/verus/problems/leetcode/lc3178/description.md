# Find the Child Who Has the Ball After K Seconds

You are given two positive integers `n` and `k`.

There are `n` children labeled from `0` to `n - 1`, standing in a line from left to right.

Initially, child `0` has a ball, and the ball is passed to the right. Every second, the current child passes the ball to an adjacent child. When the ball reaches either end (`0` or `n - 1`), the passing direction reverses.

Return the label of the child holding the ball after `k` seconds.

## Example 1

> **Input:** `n = 3`, `k = 5`  
> **Output:** `1`

## Example 2

> **Input:** `n = 5`, `k = 6`  
> **Output:** `2`

## Example 3

> **Input:** `n = 4`, `k = 2`  
> **Output:** `2`

## Constraints

- `2 <= n <= 50`
- `1 <= k <= 50`

**Note:** This is the same problem as LeetCode 2582 (Pass the Pillow).

## Starter Code

```rust
impl Solution {
    pub fn number_of_child(n: i32, k: i32) -> i32 {
        
    }
}
```

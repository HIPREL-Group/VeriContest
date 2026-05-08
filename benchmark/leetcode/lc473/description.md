# Matchsticks to Square

You are given an integer array `matchsticks` where `matchsticks[i]` is the length of the `i`th matchstick. You want to use **all** the matchsticks to make one square. You **must not break** any stick, but you can connect them, and each matchstick must be used **exactly once**.

Return `true` if you can make this square and `false` otherwise.

## Example 1:

> **Input:** `matchsticks = [1,1,2,2,2]`
> **Output:** `true`
> **Explanation:** You can form a square with side length `2`. One side uses two matchsticks of length `1`.

## Example 2:

> **Input:** `matchsticks = [3,3,3,3,4]`
> **Output:** `false`
> **Explanation:** There is no way to use all matchsticks exactly once to form a square.

## Constraints:

- `1 <= matchsticks.length <= 15`
- `1 <= matchsticks[i] <= 10^8`

## Starter Code

```rust
impl Solution {
    pub fn makesquare(matchsticks: Vec<i32>) -> bool {
        
    }
}
```

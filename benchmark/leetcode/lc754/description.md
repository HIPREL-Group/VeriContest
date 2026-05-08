# Reach a Number

You are standing at position `0` on an infinite number line. There is a destination at position `target`.

You can make some number of moves `numMoves` so that:

- On each move, you can either go left or right.
- During the `i`th move, where `1 <= i <= numMoves`, you take exactly `i` steps in the chosen direction.

Given the integer `target`, return the minimum number of moves required to reach the destination.

## Example 1:

> **Input:** target = 2
> **Output:** 3
> **Explanation:**
> On the 1st move, we step from 0 to 1.
> On the 2nd move, we step from 1 to -1.
> On the 3rd move, we step from -1 to 2.

## Example 2:

> **Input:** target = 3
> **Output:** 2
> **Explanation:**
> On the 1st move, we step from 0 to 1.
> On the 2nd move, we step from 1 to 3.

## Constraints:

- `-10^9 <= target <= 10^9`
- `target != 0`

## Starter Code

```rust
impl Solution {
    pub fn reach_number(target: i32) -> i32 {
        
    }
}
```

# Minimum Levels to Gain More Points

You are given a binary array `possible` of length `n`.

Alice and Bob are playing a game with `n` levels. If `possible[i] == 1`, then level `i` can be cleared. If `possible[i] == 0`, then level `i` cannot be cleared. Clearing a level gives `+1` point, and failing a level gives `-1` point.

Alice plays a prefix of levels in order, starting from level `0`. Bob plays all remaining levels.

Return the minimum number of levels Alice should play so that Alice gets strictly more points than Bob. If no such split exists, return `-1`.

Each player must play at least one level.

## Example 1:

> **Input:** possible = [1,0,1,0]
> **Output:** 1
> **Explanation:**
> - If Alice plays 1 level: Alice = 1, Bob = -1.
> - If Alice plays 2 levels: Alice = 0, Bob = 0.
> - If Alice plays 3 levels: Alice = 1, Bob = -1.
> The minimum is 1.

## Example 2:

> **Input:** possible = [1,1,1,1,1]
> **Output:** 3
> **Explanation:**
> - If Alice plays 1 level: Alice = 1, Bob = 4.
> - If Alice plays 2 levels: Alice = 2, Bob = 3.
> - If Alice plays 3 levels: Alice = 3, Bob = 2.
> The minimum is 3.

## Example 3:

> **Input:** possible = [0,0]
> **Output:** -1
> **Explanation:**
> The only split gives Alice = -1 and Bob = -1, so Alice is not strictly ahead.

## Constraints:

- `2 <= n == possible.length <= 10^5`
- `possible[i]` is either `0` or `1`

## Starter Code

```rust
impl Solution {
    pub fn minimum_levels(possible: Vec<i32>) -> i32 {
        
    }
}
```

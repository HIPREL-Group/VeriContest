# Alice and Bob Playing Flower Game

Alice and Bob play a turn-based game with two lanes of flowers. There are `x` flowers in the first lane and `y` flowers in the second lane.

- Alice moves first.
- On each turn, a player chooses one lane and picks exactly one flower from that lane.
- If both lanes are empty at the end of a turn, the current player wins.

Given integers `n` and `m`, count how many pairs `(x, y)` satisfy:

- `1 <= x <= n`
- `1 <= y <= m`
- Alice wins the game.

Return the number of valid pairs.

## Example 1:

> **Input:** n = 3, m = 2  
> **Output:** 3  
> **Explanation:** Valid pairs are (1,2), (2,1), and (3,2).

## Example 2:

> **Input:** n = 1, m = 1  
> **Output:** 0  
> **Explanation:** No pair makes Alice win.

## Constraints:

- `1 <= n, m <= 10^5`

## Starter Code

```dafny
predicate flower_game_pre(n: int, m: int)

predicate flower_game_post(n: int, m: int, result: int)
  requires flower_game_pre(n, m)

method flower_game(n: int, m: int) returns (result: int)
  requires flower_game_pre(n, m)
  ensures flower_game_post(n, m, result)
```

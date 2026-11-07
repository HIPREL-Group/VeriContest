# Predict the Winner

You are given an integer array `nums`. Two players are playing a game with this array: player 1 and player 2.

Player 1 and player 2 take turns, with player 1 starting first. Both players start the game with a score of `0`. At each turn, the player takes one of the numbers from either end of the array, that is, `nums[0]` or `nums[nums.length - 1]`, which reduces the size of the array by `1`. The player adds the chosen number to their score. The game ends when there are no more elements in the array.

Return `true` if Player 1 can win the game. If the scores of both players are equal, then player 1 is still the winner, and you should also return `true`. You may assume that both players are playing optimally.

## Example 1:

> **Input:** nums = [1,5,2]
> **Output:** false
> **Explanation:** Initially, player 1 can choose between 1 and 2.
> If he chooses 2, then player 2 can choose between 1 and 5 and will choose 5.
> If player 1 chooses 1 instead, then player 2 can choose between 5 and 2 and will again choose 5.
> So player 1 can never become the winner.

## Example 2:

> **Input:** nums = [1,5,233,7]
> **Output:** true
> **Explanation:** Player 1 first chooses 1.
> Then player 2 has to choose between 5 and 7.
> No matter which number player 2 chooses, player 1 can then choose 233,
> so player 1 finishes with a higher score.

## Constraints:

- `1 <= nums.length <= 20`
- `0 <= nums[i] <= 10^7`

## Starter Code

```rust
impl Solution {
    pub fn predict_the_winner(nums: Vec<i32>) -> bool {
        
    }
}
```

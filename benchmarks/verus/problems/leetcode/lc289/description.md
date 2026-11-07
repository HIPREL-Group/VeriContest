# Game of Life

According to [Wikipedia's article](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life): "The **Game of Life**, also known simply as **Life**, is a cellular automaton devised by the British mathematician John Horton Conway in 1970."

The board is made up of an `m x n` grid of cells, where each cell has an initial state: **live** (represented by a `1`) or **dead** (represented by a `0`). Each cell interacts with its eight neighbors (horizontal, vertical, diagonal) using the following four rules:

- Any live cell with fewer than two live neighbors dies as if caused by under-population.
- Any live cell with two or three live neighbors lives on to the next generation.
- Any live cell with more than three live neighbors dies, as if by over-population.
- Any dead cell with exactly three live neighbors becomes a live cell, as if by reproduction.

The next state is computed by applying the above rules simultaneously to every cell in the current state of the board.

Given the current state of the board, update the board in-place to its next state.

## Example 1:

> **Input:** board = [[0,1,0],[0,0,1],[1,1,1],[0,0,0]]
> **Output:** [[0,0,0],[1,0,1],[0,1,1],[0,1,0]]

## Example 2:

> **Input:** board = [[1,1],[1,0]]
> **Output:** [[1,1],[1,1]]

## Constraints:

- `m == board.length`
- `n == board[i].length`
- `1 <= m, n <= 25`
- `board[i][j]` is `0` or `1`

## Follow up:

- Could you solve it in-place while updating all cells simultaneously?
- The board is conceptually infinite. How would you handle active cells reaching the border?

## Starter Code

```rust
impl Solution {
    pub fn game_of_life(board: &mut Vec<Vec<i32>>) {
        
    }
}
```

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_index(board: Seq<Vec<i32>>, r: int, c: int) -> bool {
        0 <= r < board.len() && 0 <= c < board[r].len()
    }

    pub open spec fn live_at(board: Seq<Vec<i32>>, r: int, c: int) -> int {
        if Self::valid_index(board, r, c) && board[r][c] == 1 { 1 } else { 0 }
    }

    pub open spec fn live_neighbors(board: Seq<Vec<i32>>, row: int, col: int) -> int {
        Self::live_at(board, row - 1, col - 1)
        + Self::live_at(board, row - 1, col)
        + Self::live_at(board, row - 1, col + 1)
        + Self::live_at(board, row, col - 1)
        + Self::live_at(board, row, col + 1)
        + Self::live_at(board, row + 1, col - 1)
        + Self::live_at(board, row + 1, col)
        + Self::live_at(board, row + 1, col + 1)
    }

    pub open spec fn next_state(board: Seq<Vec<i32>>, row: int, col: int) -> i32 {
        let n = Self::live_neighbors(board, row, col);
        if board[row][col] == 1 {
            if n < 2 || n > 3 { 0 } else { 1 }
        } else {
            if n == 3 { 1 } else { 0 }
        }
    }

    pub fn game_of_life(board: &mut Vec<Vec<i32>>)
        requires
            1 <= old(board)@.len() <= 25,
            1 <= old(board)@[0].len() <= 25,
            forall |r: int| 0 <= r < old(board)@.len() ==> #[trigger] old(board)@[r].len() == old(board)@[0].len(),
            forall |r: int, c: int|
                0 <= r < old(board)@.len() && 0 <= c < old(board)@[r].len() ==> (#[trigger] old(board)@[r][c] == 0 || old(board)@[r][c] == 1),
        ensures
            board@.len() == old(board)@.len(),
            forall |r: int| 0 <= r < board@.len() ==> #[trigger] board@[r].len() == old(board)@[r].len(),
            forall |r: int, c: int|
                0 <= r < board@.len() && 0 <= c < board@[r].len() ==> #[trigger] board@[r][c] == Self::next_state(old(board)@, r, c),
    {
    }
}

}

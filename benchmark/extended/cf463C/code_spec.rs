use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_flat_index(n: int, idx: int) -> bool {
        0 < n && 0 <= idx < n * n
    }

    pub open spec fn row_of(n: int, idx: int) -> int
        recommends
            Self::valid_flat_index(n, idx),
    {
        idx / n
    }

    pub open spec fn col_of(n: int, idx: int) -> int
        recommends
            Self::valid_flat_index(n, idx),
    {
        idx % n
    }

    pub open spec fn main_diag_id_of_index(n: int, idx: int) -> int
        recommends
            Self::valid_flat_index(n, idx),
    {
        Self::row_of(n, idx) + (n - 1 - Self::col_of(n, idx))
    }

    pub open spec fn anti_diag_id_of_index(n: int, idx: int) -> int
        recommends
            Self::valid_flat_index(n, idx),
    {
        Self::row_of(n, idx) + Self::col_of(n, idx)
    }

    pub open spec fn index_parity(n: int, idx: int) -> int
        recommends
            Self::valid_flat_index(n, idx),
    {
        (Self::row_of(n, idx) + Self::col_of(n, idx)) % 2
    }

    pub open spec fn diag_main_sum_upto(board: Seq<i64>, n: int, diag: int, end: int) -> int
        recommends
            0 < n,
            board.len() == n * n,
            0 <= end <= board.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::diag_main_sum_upto(board, n, diag, end - 1) + if Self::main_diag_id_of_index(n, end - 1) == diag {
                board[end - 1] as int
            } else {
                0
            }
        }
    }

    pub open spec fn diag_anti_sum_upto(board: Seq<i64>, n: int, diag: int, end: int) -> int
        recommends
            0 < n,
            board.len() == n * n,
            0 <= end <= board.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::diag_anti_sum_upto(board, n, diag, end - 1) + if Self::anti_diag_id_of_index(n, end - 1) == diag {
                board[end - 1] as int
            } else {
                0
            }
        }
    }

    pub open spec fn diag_main_sum(board: Seq<i64>, n: int, diag: int) -> int
        recommends
            0 < n,
            board.len() == n * n,
    {
        Self::diag_main_sum_upto(board, n, diag, board.len() as int)
    }

    pub open spec fn diag_anti_sum(board: Seq<i64>, n: int, diag: int) -> int
        recommends
            0 < n,
            board.len() == n * n,
    {
        Self::diag_anti_sum_upto(board, n, diag, board.len() as int)
    }

    pub open spec fn cell_score_at_index(board: Seq<i64>, n: int, idx: int) -> int
        recommends
            0 < n,
            board.len() == n * n,
            Self::valid_flat_index(n, idx),
    {
        Self::diag_main_sum(board, n, Self::main_diag_id_of_index(n, idx))
            + Self::diag_anti_sum(board, n, Self::anti_diag_id_of_index(n, idx))
            - board[idx] as int
    }

    pub fn best_bishops(n: usize, board: Vec<i64>) -> (result: (i128, usize, usize))
        requires
            2 <= n <= 2000,
            board.len() == n * n,
            2 <= board.len(),
            board.len() <= 4_000_000,
            forall |k: int| 0 <= k < board.len() ==> 0 <= #[trigger] board[k] <= 1_000_000_000,
        ensures
            result.1 < board.len(),
            result.2 < board.len(),
            Self::index_parity(n as int, result.1 as int) == 0,
            Self::index_parity(n as int, result.2 as int) == 1,
            result.0 as int == Self::cell_score_at_index(board@, n as int, result.1 as int)
                + Self::cell_score_at_index(board@, n as int, result.2 as int),
            forall |idx: int| 0 <= idx < board.len() && Self::index_parity(n as int, idx) == 0 ==> Self::cell_score_at_index(board@, n as int, idx)
                <= Self::cell_score_at_index(board@, n as int, result.1 as int),
            forall |idx: int| 0 <= idx < board.len() && Self::index_parity(n as int, idx) == 1 ==> Self::cell_score_at_index(board@, n as int, idx)
                <= Self::cell_score_at_index(board@, n as int, result.2 as int),
    {
        let diag_len = 2 * n - 1;
        let mut main_diag = Vec::new();
        let mut anti_diag = Vec::new();
        let mut d = 0usize;
        while d < diag_len {
            main_diag.push(0i64);
            anti_diag.push(0i64);
            d = d + 1;
        }
        let mut idx = 0usize;
        while idx < board.len() {
            let r = idx / n;
            let c = idx % n;
            let main_id = r + (n - 1 - c);
            let anti_id = r + c;
            main_diag.set(main_id, main_diag[main_id] + board[idx]);
            anti_diag.set(anti_id, anti_diag[anti_id] + board[idx]);
            idx = idx + 1;
        }
        let mut best_even_idx = 0usize;
        let mut best_odd_idx = 1usize;
        let mut best_even_score = main_diag[n - 1] as i128 + anti_diag[0] as i128 - board[0] as i128;
        let mut best_odd_score = main_diag[n - 2] as i128 + anti_diag[1] as i128 - board[1] as i128;
        idx = 2;
        while idx < board.len() {
            let r = idx / n;
            let c = idx % n;
            let main_id = r + (n - 1 - c);
            let anti_id = r + c;
            let score = main_diag[main_id] as i128 + anti_diag[anti_id] as i128 - board[idx] as i128;
            if (r + c) % 2 == 0 {
                if score > best_even_score {
                    best_even_score = score;
                    best_even_idx = idx;
                }
            } else {
                if score > best_odd_score {
                    best_odd_score = score;
                    best_odd_idx = idx;
                }
            }
            idx = idx + 1;
        }
        (best_even_score + best_odd_score, best_even_idx, best_odd_idx)
    }
}

}

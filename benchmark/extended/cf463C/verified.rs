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

    proof fn lemma_row_col_bounds(n: int, idx: int)
        requires
            0 < n,
            0 <= idx < n * n,
        ensures
            0 <= Self::row_of(n, idx) < n,
            0 <= Self::col_of(n, idx) < n,
    {
        assert(0 <= idx / n);
        assert(idx / n < n) by (nonlinear_arith)
            requires
                0 < n,
                0 <= idx,
                idx < n * n,
        {
        }
        assert(0 <= idx % n < n);
    }

    proof fn lemma_main_diag_id_bounds(n: int, idx: int)
        requires
            0 < n,
            0 <= idx < n * n,
        ensures
            0 <= Self::main_diag_id_of_index(n, idx) < 2 * n - 1,
    {
        Self::lemma_row_col_bounds(n, idx);
    }

    proof fn lemma_anti_diag_id_bounds(n: int, idx: int)
        requires
            0 < n,
            0 <= idx < n * n,
        ensures
            0 <= Self::anti_diag_id_of_index(n, idx) < 2 * n - 1,
    {
        Self::lemma_row_col_bounds(n, idx);
    }

    proof fn lemma_first_two_indices(n: int)
        requires
            2 <= n,
        ensures
            Self::valid_flat_index(n, 0),
            Self::valid_flat_index(n, 1),
            Self::index_parity(n, 0) == 0,
            Self::index_parity(n, 1) == 1,
            Self::main_diag_id_of_index(n, 0) == n - 1,
            Self::anti_diag_id_of_index(n, 0) == 0,
            Self::main_diag_id_of_index(n, 1) == n - 2,
            Self::anti_diag_id_of_index(n, 1) == 1,
    {
        assert(1 < n * n) by (nonlinear_arith)
            requires
                2 <= n,
        {
        }
        assert(Self::valid_flat_index(n, 0));
        assert(Self::valid_flat_index(n, 1));
        assert(Self::row_of(n, 0) == 0);
        assert(Self::col_of(n, 0) == 0);
        
        assert(1int / n == 0int) by (nonlinear_arith)
            requires
                2 <= n,
        {
        }
        assert(1int % n == 1int) by (nonlinear_arith)
            requires
                2 <= n,
        {
        }
        assert(Self::row_of(n, 1) == 0);
        assert(Self::col_of(n, 1) == 1);
    }

    proof fn lemma_diag_main_step(board: Seq<i64>, n: int, diag: int, end: int)
        requires
            0 < n,
            board.len() == n * n,
            0 <= end < board.len(),
        ensures
            Self::diag_main_sum_upto(board, n, diag, end + 1) == Self::diag_main_sum_upto(board, n, diag, end) + if Self::main_diag_id_of_index(n, end) == diag {
                board[end] as int
            } else {
                0
            },
    {
    }

    proof fn lemma_diag_anti_step(board: Seq<i64>, n: int, diag: int, end: int)
        requires
            0 < n,
            board.len() == n * n,
            0 <= end < board.len(),
        ensures
            Self::diag_anti_sum_upto(board, n, diag, end + 1) == Self::diag_anti_sum_upto(board, n, diag, end) + if Self::anti_diag_id_of_index(n, end) == diag {
                board[end] as int
            } else {
                0
            },
    {
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
        while d < diag_len
            invariant
                2 <= n <= 2000,
                board.len() == n * n,
                2 <= board.len(),
                board.len() <= 4_000_000,
                forall |k: int| 0 <= k < board.len() ==> 0 <= #[trigger] board[k] <= 1_000_000_000,
                diag_len == 2 * n - 1,
                d <= diag_len,
                main_diag.len() == d,
                anti_diag.len() == d,
                forall |j: int| 0 <= j < d ==> #[trigger] main_diag[j] == 0,
                forall |j: int| 0 <= j < d ==> #[trigger] anti_diag[j] == 0,
            decreases diag_len - d,
        {
            main_diag.push(0i64);
            anti_diag.push(0i64);
            d = d + 1;
        }
        let mut idx = 0usize;
        while idx < board.len()
            invariant
                2 <= n <= 2000,
                board.len() == n * n,
                2 <= board.len(),
                board.len() <= 4_000_000,
                forall |k: int| 0 <= k < board.len() ==> 0 <= #[trigger] board[k] <= 1_000_000_000,
                diag_len == 2 * n - 1,
                main_diag.len() == diag_len,
                anti_diag.len() == diag_len,
                idx <= board.len(),
                forall |j: int| 0 <= j < diag_len ==> 0 <= #[trigger] main_diag[j] <= idx as int * 1_000_000_000,
                forall |j: int| 0 <= j < diag_len ==> 0 <= #[trigger] anti_diag[j] <= idx as int * 1_000_000_000,
                forall |j: int| 0 <= j < diag_len ==> main_diag[j] as int == Self::diag_main_sum_upto(board@, n as int, j, idx as int),
                forall |j: int| 0 <= j < diag_len ==> anti_diag[j] as int == Self::diag_anti_sum_upto(board@, n as int, j, idx as int),
            decreases board.len() - idx,
        {
            let r = idx / n;
            let c = idx % n;
            let main_id = r + (n - 1 - c);
            let anti_id = r + c;
            proof {
                Self::lemma_main_diag_id_bounds(n as int, idx as int);
                Self::lemma_anti_diag_id_bounds(n as int, idx as int);
            }
            let ghost old_main = main_diag@;
            let ghost old_anti = anti_diag@;
            main_diag.set(main_id, main_diag[main_id] + board[idx]);
            anti_diag.set(anti_id, anti_diag[anti_id] + board[idx]);
            proof {
                assert forall |j: int| 0 <= j < diag_len implies 0 <= #[trigger] main_diag[j] <= (idx as int + 1) * 1_000_000_000 by {
                    if j == main_id as int {
                        assert(old_main[j] as int == Self::diag_main_sum_upto(board@, n as int, j, idx as int));
                        assert(old_main[j] <= idx as int * 1_000_000_000);
                        assert(0 <= board[idx as int] <= 1_000_000_000);
                    } else {
                        assert(main_diag[j] == old_main[j]);
                        assert(0 <= old_main[j] <= idx as int * 1_000_000_000);
                    }
                }
                assert forall |j: int| 0 <= j < diag_len implies 0 <= #[trigger] anti_diag[j] <= (idx as int + 1) * 1_000_000_000 by {
                    if j == anti_id as int {
                        assert(old_anti[j] as int == Self::diag_anti_sum_upto(board@, n as int, j, idx as int));
                        assert(old_anti[j] <= idx as int * 1_000_000_000);
                        assert(0 <= board[idx as int] <= 1_000_000_000);
                    } else {
                        assert(anti_diag[j] == old_anti[j]);
                        assert(0 <= old_anti[j] <= idx as int * 1_000_000_000);
                    }
                }
                assert forall |j: int| 0 <= j < diag_len implies #[trigger] main_diag[j] as int == Self::diag_main_sum_upto(board@, n as int, j, idx as int + 1) by {
                    Self::lemma_diag_main_step(board@, n as int, j, idx as int);
                    if j == main_id as int {
                        assert(Self::main_diag_id_of_index(n as int, idx as int) == j);
                    } else {
                        assert(Self::main_diag_id_of_index(n as int, idx as int) != j);
                        assert(main_diag[j] == old_main[j]);
                    }
                }
                assert forall |j: int| 0 <= j < diag_len implies #[trigger] anti_diag[j] as int == Self::diag_anti_sum_upto(board@, n as int, j, idx as int + 1) by {
                    Self::lemma_diag_anti_step(board@, n as int, j, idx as int);
                    if j == anti_id as int {
                        assert(Self::anti_diag_id_of_index(n as int, idx as int) == j);
                    } else {
                        assert(Self::anti_diag_id_of_index(n as int, idx as int) != j);
                        assert(anti_diag[j] == old_anti[j]);
                    }
                }
            }
            idx = idx + 1;
        }
        let mut best_even_idx = 0usize;
        let mut best_odd_idx = 1usize;
        proof {
            Self::lemma_first_two_indices(n as int);
            assert(main_diag[n as int - 1] as int == Self::diag_main_sum(board@, n as int, n as int - 1));
            assert(anti_diag[0] as int == Self::diag_anti_sum(board@, n as int, 0));
            assert(main_diag[n as int - 2] as int == Self::diag_main_sum(board@, n as int, n as int - 2));
            assert(anti_diag[1] as int == Self::diag_anti_sum(board@, n as int, 1));
        }
        let mut best_even_score = main_diag[n - 1] as i128 + anti_diag[0] as i128 - board[0] as i128;
        let mut best_odd_score = main_diag[n - 2] as i128 + anti_diag[1] as i128 - board[1] as i128;
        idx = 2;
        while idx < board.len()
            invariant
                2 <= n <= 2000,
                board.len() == n * n,
                2 <= board.len(),
                board.len() <= 4_000_000,
                forall |k: int| 0 <= k < board.len() ==> 0 <= #[trigger] board[k] <= 1_000_000_000,
                diag_len == 2 * n - 1,
                main_diag.len() == diag_len,
                anti_diag.len() == diag_len,
                forall |j: int| 0 <= j < diag_len ==> 0 <= #[trigger] main_diag[j] <= 4_000_000_000_000_000,
                forall |j: int| 0 <= j < diag_len ==> 0 <= #[trigger] anti_diag[j] <= 4_000_000_000_000_000,
                forall |j: int| 0 <= j < diag_len ==> main_diag[j] as int == Self::diag_main_sum(board@, n as int, j),
                forall |j: int| 0 <= j < diag_len ==> anti_diag[j] as int == Self::diag_anti_sum(board@, n as int, j),
                2 <= idx <= board.len(),
                best_even_idx < idx,
                best_odd_idx < idx,
                Self::index_parity(n as int, best_even_idx as int) == 0,
                Self::index_parity(n as int, best_odd_idx as int) == 1,
                best_even_score as int == Self::cell_score_at_index(board@, n as int, best_even_idx as int),
                best_odd_score as int == Self::cell_score_at_index(board@, n as int, best_odd_idx as int),
                -1_000_000_000 <= best_even_score as int <= 8_000_000_000_000_000,
                -1_000_000_000 <= best_odd_score as int <= 8_000_000_000_000_000,
                forall |j: int| 0 <= j < idx && Self::index_parity(n as int, j) == 0 ==> #[trigger] Self::cell_score_at_index(board@, n as int, j) <= best_even_score as int,
                forall |j: int| 0 <= j < idx && Self::index_parity(n as int, j) == 1 ==> #[trigger] Self::cell_score_at_index(board@, n as int, j) <= best_odd_score as int,
            decreases board.len() - idx,
        {
            let r = idx / n;
            let c = idx % n;
            let main_id = r + (n - 1 - c);
            let anti_id = r + c;
            proof {
                Self::lemma_main_diag_id_bounds(n as int, idx as int);
                Self::lemma_anti_diag_id_bounds(n as int, idx as int);
                assert(main_id < diag_len);
                assert(anti_id < diag_len);
            }
            let score = main_diag[main_id] as i128 + anti_diag[anti_id] as i128 - board[idx] as i128;
            proof {
                assert(main_diag[main_id as int] as int == Self::diag_main_sum(board@, n as int, main_id as int));
                assert(anti_diag[anti_id as int] as int == Self::diag_anti_sum(board@, n as int, anti_id as int));
                assert(score as int == Self::cell_score_at_index(board@, n as int, idx as int));
                assert(-1_000_000_000 <= score as int <= 8_000_000_000_000_000);
            }
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
            proof {
                if Self::index_parity(n as int, idx as int) == 0 {
                    assert((r + c) % 2 == 0);
                    if best_even_idx == idx {
                        assert(best_even_score as int == Self::cell_score_at_index(board@, n as int, idx as int));
                    }
                    assert forall |j: int| 0 <= j < idx as int + 1 && Self::index_parity(n as int, j) == 0 implies #[trigger] Self::cell_score_at_index(board@, n as int, j) <= best_even_score as int by {
                        if j == idx as int {
                            assert(best_even_score as int == Self::cell_score_at_index(board@, n as int, idx as int) || Self::cell_score_at_index(board@, n as int, idx as int) <= best_even_score as int);
                        } else {
                            assert(0 <= j < idx as int);
                            if best_even_idx == idx {
                                assert(Self::cell_score_at_index(board@, n as int, j) <= score as int);
                            }
                        }
                    }
                    assert forall |j: int| 0 <= j < idx as int + 1 && Self::index_parity(n as int, j) == 1 implies #[trigger] Self::cell_score_at_index(board@, n as int, j) <= best_odd_score as int by {
                        assert(0 <= j < idx as int);
                        assert(Self::cell_score_at_index(board@, n as int, j) <= best_odd_score as int);
                    }
                } else {
                    assert((r + c) % 2 != 0);
                    if best_odd_idx == idx {
                        assert(best_odd_score as int == Self::cell_score_at_index(board@, n as int, idx as int));
                    }
                    assert forall |j: int| 0 <= j < idx as int + 1 && Self::index_parity(n as int, j) == 1 implies #[trigger] Self::cell_score_at_index(board@, n as int, j) <= best_odd_score as int by {
                        if j == idx as int {
                            assert(best_odd_score as int == Self::cell_score_at_index(board@, n as int, idx as int) || Self::cell_score_at_index(board@, n as int, idx as int) <= best_odd_score as int);
                        } else {
                            assert(0 <= j < idx as int);
                            if best_odd_idx == idx {
                                assert(Self::cell_score_at_index(board@, n as int, j) <= score as int);
                            }
                        }
                    }
                    assert forall |j: int| 0 <= j < idx as int + 1 && Self::index_parity(n as int, j) == 0 implies #[trigger] Self::cell_score_at_index(board@, n as int, j) <= best_even_score as int by {
                        assert(0 <= j < idx as int);
                        assert(Self::cell_score_at_index(board@, n as int, j) <= best_even_score as int);
                    }
                }
                assert(-1_000_000_000 <= best_even_score as int <= 8_000_000_000_000_000);
                assert(-1_000_000_000 <= best_odd_score as int <= 8_000_000_000_000_000);
            }
            idx = idx + 1;
        }
        proof {
            assert(idx == board.len());
            assert(best_even_score as int == Self::cell_score_at_index(board@, n as int, best_even_idx as int));
            assert(best_odd_score as int == Self::cell_score_at_index(board@, n as int, best_odd_idx as int));
            assert((best_even_score + best_odd_score) as int == best_even_score as int + best_odd_score as int);
        }
        (best_even_score + best_odd_score, best_even_idx, best_odd_idx)
    }
}

}
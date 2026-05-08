use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn big_cost() -> int {
        1_000_000_000int
    }

    pub open spec fn col_count_prefix(grid: Seq<Vec<i32>>, col: int, val: int, rows: int) -> int
        recommends
            grid.len() > 0,
            0 <= rows <= grid.len(),
            0 <= col < grid[0].len(),
            0 <= val < 10,
        decreases rows,
    {
        if rows <= 0 {
            0
        } else {
            Self::col_count_prefix(grid, col, val, rows - 1)
                + if grid[rows - 1][col] == val as i32 { 1int } else { 0int }
        }
    }

    pub open spec fn col_cost(grid: Seq<Vec<i32>>, col: int, val: int) -> int
        recommends
            grid.len() > 0,
            0 <= col < grid[0].len(),
            0 <= val < 10,
    {
        grid.len() as int - Self::col_count_prefix(grid, col, val, grid.len() as int)
    }

    pub open spec fn min_cost_prefix_last(grid: Seq<Vec<i32>>, cols: int, last: int) -> int
        recommends
            grid.len() > 0,
            1 <= cols <= grid[0].len(),
            0 <= last < 10,
        decreases cols, 0int,
    {
        if cols <= 1 {
            Self::col_cost(grid, 0, last)
        } else {
            Self::col_cost(grid, cols - 1, last)
                + Self::min_prev_prefix(grid, cols - 1, last, 10)
        }
    }

    pub open spec fn min_prev_prefix(grid: Seq<Vec<i32>>, cols: int, last: int, upto: int) -> int
        recommends
            grid.len() > 0,
            1 <= cols <= grid[0].len(),
            0 <= last < 10,
            0 <= upto <= 10,
        decreases cols, 1int, upto,
    {
        if upto <= 0 {
            Self::big_cost()
        } else {
            let rest = Self::min_prev_prefix(grid, cols, last, upto - 1);
            let cand = upto - 1;
            if cand == last {
                rest
            } else {
                let cur = Self::min_cost_prefix_last(grid, cols, cand);
                if cur <= rest { cur } else { rest }
            }
        }
    }

    pub open spec fn min_total_prefix(grid: Seq<Vec<i32>>, cols: int, upto: int) -> int
        recommends
            grid.len() > 0,
            1 <= cols <= grid[0].len(),
            0 <= upto <= 10,
        decreases upto,
    {
        if upto <= 0 {
            Self::big_cost()
        } else {
            let rest = Self::min_total_prefix(grid, cols, upto - 1);
            let cand = upto - 1;
            let cur = Self::min_cost_prefix_last(grid, cols, cand);
            if cur <= rest { cur } else { rest }
        }
    }

    pub open spec fn min_operations_spec(grid: Seq<Vec<i32>>) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
    {
        Self::min_total_prefix(grid, grid[0].len() as int, 10)
    }

    pub open spec fn min_vec_prefix(dp: Seq<i64>, forbid: int, upto: int) -> int
        recommends
            dp.len() == 10,
            0 <= forbid < 10,
            0 <= upto <= 10,
        decreases upto,
    {
        if upto <= 0 {
            Self::big_cost()
        } else {
            let rest = Self::min_vec_prefix(dp, forbid, upto - 1);
            let cand = upto - 1;
            if cand == forbid {
                rest
            } else {
                let cur = dp[cand] as int;
                if cur <= rest { cur } else { rest }
            }
        }
    }

    pub open spec fn min_vec_all_prefix(dp: Seq<i64>, upto: int) -> int
        recommends
            dp.len() == 10,
            0 <= upto <= 10,
        decreases upto,
    {
        if upto <= 0 {
            Self::big_cost()
        } else {
            let rest = Self::min_vec_all_prefix(dp, upto - 1);
            let cand = upto - 1;
            let cur = dp[cand] as int;
            if cur <= rest { cur } else { rest }
        }
    }

    proof fn lemma_col_count_prefix_bounds(grid: Seq<Vec<i32>>, col: int, val: int, rows: int)
        requires
            grid.len() > 0,
            0 <= rows <= grid.len(),
            0 <= col < grid[0].len(),
            0 <= val < 10,
        ensures
            0 <= Self::col_count_prefix(grid, col, val, rows) <= rows,
        decreases rows,
    {
        if rows > 0 {
            Self::lemma_col_count_prefix_bounds(grid, col, val, rows - 1);
        }
    }

    proof fn lemma_min_vec_prefix_eq_spec(dp: Seq<i64>, grid: Seq<Vec<i32>>, cols: int, forbid: int, upto: int)
        requires
            grid.len() > 0,
            dp.len() == 10,
            1 <= cols <= grid[0].len(),
            0 <= forbid < 10,
            0 <= upto <= 10,
            forall |u: int| 0 <= u < 10 ==> dp[u] as int == #[trigger] Self::min_cost_prefix_last(grid, cols, u),
        ensures
            Self::min_vec_prefix(dp, forbid, upto) == Self::min_prev_prefix(grid, cols, forbid, upto),
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_min_vec_prefix_eq_spec(dp, grid, cols, forbid, upto - 1);
            let rest_vec = Self::min_vec_prefix(dp, forbid, upto - 1);
            let rest_spec = Self::min_prev_prefix(grid, cols, forbid, upto - 1);
            assert(rest_vec == rest_spec);
            let cand = upto - 1;
            if cand == forbid {
                assert(Self::min_vec_prefix(dp, forbid, upto) == rest_vec);
                assert(Self::min_prev_prefix(grid, cols, forbid, upto) == rest_spec);
            } else {
                assert(0 <= cand < 10);
                assert(dp[cand] as int == Self::min_cost_prefix_last(grid, cols, cand));
                assert(Self::min_vec_prefix(dp, forbid, upto) == if dp[cand] as int <= rest_vec { dp[cand] as int } else { rest_vec });
                assert(Self::min_prev_prefix(grid, cols, forbid, upto) ==
                    if Self::min_cost_prefix_last(grid, cols, cand) <= rest_spec {
                        Self::min_cost_prefix_last(grid, cols, cand)
                    } else {
                        rest_spec
                    });
            }
        }
    }

    proof fn lemma_min_vec_prefix_nonneg(dp: Seq<i64>, forbid: int, upto: int)
        requires
            dp.len() == 10,
            0 <= forbid < 10,
            0 <= upto <= 10,
            forall |u: int| 0 <= u < 10 ==> 0 <= #[trigger] dp[u] as int,
        ensures
            0 <= Self::min_vec_prefix(dp, forbid, upto),
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_min_vec_prefix_nonneg(dp, forbid, upto - 1);
        }
    }

    proof fn lemma_min_vec_prefix_le_entry(dp: Seq<i64>, forbid: int, upto: int, cand: int)
        requires
            dp.len() == 10,
            0 <= forbid < 10,
            0 < upto <= 10,
            0 <= cand < upto,
            cand != forbid,
        ensures
            Self::min_vec_prefix(dp, forbid, upto) <= dp[cand] as int,
        decreases upto,
    {
        if upto > 1 {
            let last = upto - 1;
            if cand < last {
                Self::lemma_min_vec_prefix_le_entry(dp, forbid, upto - 1, cand);
            }
        }
    }

    proof fn lemma_min_vec_all_prefix_eq_spec(dp: Seq<i64>, grid: Seq<Vec<i32>>, cols: int, upto: int)
        requires
            grid.len() > 0,
            dp.len() == 10,
            1 <= cols <= grid[0].len(),
            0 <= upto <= 10,
            forall |u: int| 0 <= u < 10 ==> dp[u] as int == #[trigger] Self::min_cost_prefix_last(grid, cols, u),
        ensures
            Self::min_vec_all_prefix(dp, upto) == Self::min_total_prefix(grid, cols, upto),
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_min_vec_all_prefix_eq_spec(dp, grid, cols, upto - 1);
        }
    }

    proof fn lemma_min_vec_all_prefix_nonneg(dp: Seq<i64>, upto: int)
        requires
            dp.len() == 10,
            0 <= upto <= 10,
            forall |u: int| 0 <= u < 10 ==> 0 <= #[trigger] dp[u] as int,
        ensures
            0 <= Self::min_vec_all_prefix(dp, upto),
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_min_vec_all_prefix_nonneg(dp, upto - 1);
        }
    }

    proof fn lemma_min_vec_all_prefix_le_entry(dp: Seq<i64>, upto: int, cand: int)
        requires
            dp.len() == 10,
            0 < upto <= 10,
            0 <= cand < upto,
        ensures
            Self::min_vec_all_prefix(dp, upto) <= dp[cand] as int,
        decreases upto,
    {
        if upto > 1 {
            let last = upto - 1;
            if cand < last {
                Self::lemma_min_vec_all_prefix_le_entry(dp, upto - 1, cand);
            }
        }
    }

    pub fn minimum_operations(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 1000,
            1 <= grid[0].len() <= 1000,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
        ensures
            result as int == Self::min_operations_spec(grid@),
    {
        let m = grid.len();
        let n = grid[0].len();
        let m_i64 = m as i64;

        let mut dp_prev: Vec<i64> = Vec::new();
        let mut v: usize = 0;
        while v < 10
            invariant
                m == grid.len(),
                n == grid[0].len(),
                1 <= m <= 1000,
                1 <= n <= 1000,
                m_i64 == m as i64,
                forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
                forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
                0 <= v <= 10,
                dp_prev.len() == v,
                forall |t: int| 0 <= t < dp_prev.len() ==>
                    #[trigger] dp_prev[t] as int == Self::min_cost_prefix_last(grid@, 1, t),
                forall |t: int| 0 <= t < dp_prev.len() ==> 0 <= #[trigger] dp_prev[t] as int <= m as int,
            decreases 10 - v,
        {
            let mut matches: i64 = 0;
            let mut i: usize = 0;
            while i < m
                invariant
                    m == grid.len(),
                    n == grid[0].len(),
                    1 <= m <= 1000,
                    1 <= n <= 1000,
                    0 <= v < 10,
                    0 <= i <= m,
                    0 <= matches as int <= i as int,
                    matches as int == Self::col_count_prefix(grid@, 0, v as int, i as int),
                    forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
                    forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
                decreases m - i,
            {
                proof {
                    assert(i < grid.len());
                    assert(grid[i as int].len() == grid[0].len());
                    assert(0 < grid[i as int].len());
                }
                if grid[i][0] == v as i32 {
                    matches = matches + 1;
                }
                i = i + 1;
            }
            let cost = m_i64 - matches;
            let ghost before = dp_prev@;
            dp_prev.push(cost);
            proof {
                assert(dp_prev@ == before.push(cost));
                assert(matches as int == Self::col_count_prefix(grid@, 0, v as int, m as int));
                Self::lemma_col_count_prefix_bounds(grid@, 0, v as int, m as int);
                assert(cost as int == Self::col_cost(grid@, 0, v as int));
                assert(Self::min_cost_prefix_last(grid@, 1, v as int) == Self::col_cost(grid@, 0, v as int));
                assert(0 <= cost as int <= m as int);
            }
            v = v + 1;
        }

        let mut col: usize = 1;
        while col < n
            invariant
                m == grid.len(),
                n == grid[0].len(),
                1 <= m <= 1000,
                1 <= n <= 1000,
                m_i64 == m as i64,
                1 <= col <= n,
                dp_prev.len() == 10,
                forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
                forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
                forall |t: int| 0 <= t < 10 ==> #[trigger] dp_prev[t] as int == Self::min_cost_prefix_last(grid@, col as int, t),
                forall |t: int| 0 <= t < 10 ==> 0 <= #[trigger] dp_prev[t] as int <= (col as int) * (m as int),
            decreases n - col,
        {
            let mut dp_cur: Vec<i64> = Vec::new();
            v = 0;
            while v < 10
                invariant
                    m == grid.len(),
                    n == grid[0].len(),
                    1 <= m <= 1000,
                    1 <= n <= 1000,
                    m_i64 == m as i64,
                    1 <= col < n,
                    0 <= v <= 10,
                    dp_prev.len() == 10,
                    dp_cur.len() == v,
                    forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
                    forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
                    forall |t: int| 0 <= t < 10 ==> #[trigger] dp_prev[t] as int == Self::min_cost_prefix_last(grid@, col as int, t),
                    forall |t: int| 0 <= t < 10 ==> 0 <= #[trigger] dp_prev[t] as int <= (col as int) * (m as int),
                    forall |t: int| 0 <= t < dp_cur.len() ==> #[trigger] dp_cur[t] as int == Self::min_cost_prefix_last(grid@, col as int + 1, t),
                    forall |t: int| 0 <= t < dp_cur.len() ==> 0 <= #[trigger] dp_cur[t] as int <= (col as int + 1) * (m as int),
                decreases 10 - v,
            {
                let mut matches: i64 = 0;
                let mut i: usize = 0;
                while i < m
                    invariant
                        m == grid.len(),
                        n == grid[0].len(),
                        1 <= m <= 1000,
                        1 <= n <= 1000,
                        1 <= col < n,
                        0 <= v < 10,
                        0 <= i <= m,
                        0 <= matches as int <= i as int,
                        matches as int == Self::col_count_prefix(grid@, col as int, v as int, i as int),
                        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
                        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
                    decreases m - i,
                {
                    proof {
                        assert(i < grid.len());
                        assert(grid[i as int].len() == grid[0].len());
                        assert(col < grid[i as int].len());
                    }
                    if grid[i][col] == v as i32 {
                        matches = matches + 1;
                    }
                    i = i + 1;
                }
                let cost = m_i64 - matches;

                let mut best: i64 = 1_000_000_000;
                let mut u: usize = 0;
                while u < 10
                    invariant
                        1 <= col < n,
                        1 <= m <= 1000,
                        0 <= v < 10,
                        0 <= u <= 10,
                        dp_prev.len() == 10,
                        best as int == Self::min_vec_prefix(dp_prev@, v as int, u as int),
                        0 <= best as int <= 1_000_000_000,
                        forall |t: int| 0 <= t < 10 ==> 0 <= #[trigger] dp_prev[t] as int <= (col as int) * (m as int),
                    decreases 10 - u,
                {
                    if u != v && dp_prev[u] < best {
                        best = dp_prev[u];
                    }
                    proof {
                        if u as int != v as int {
                            let old = Self::min_vec_prefix(dp_prev@, v as int, u as int);
                            let cur = dp_prev@[u as int] as int;
                            let newv = Self::min_vec_prefix(dp_prev@, v as int, u as int + 1);
                            assert(newv == if cur <= old { cur } else { old });
                        } else {
                            assert(Self::min_vec_prefix(dp_prev@, v as int, u as int + 1)
                                == Self::min_vec_prefix(dp_prev@, v as int, u as int));
                        }
                    }
                    u = u + 1;
                }

                proof {
                    Self::lemma_min_vec_prefix_nonneg(dp_prev@, v as int, 10);
                    let alt: int = if v == 0 { 1 } else { 0 };
                    assert(0 <= alt < 10);
                    assert(alt != v as int);
                    Self::lemma_min_vec_prefix_le_entry(dp_prev@, v as int, 10, alt);
                    assert(best as int <= dp_prev[alt as int] as int);
                    assert(dp_prev[alt as int] as int <= (col as int) * (m as int));
                    assert(0 <= best as int <= (col as int) * (m as int));
                    assert(0 <= cost as int <= m as int);
                    assert(0 <= cost as int + best as int <= (col as int + 1) * (m as int)) by (nonlinear_arith)
                        requires
                            0 <= cost as int,
                            cost as int <= m as int,
                            0 <= best as int,
                            best as int <= (col as int) * (m as int),
                            1 <= m as int,
                    {};
                    assert(0 <= best as int <= 1_000_000_000);
                    assert(0 <= cost as int <= 1000);
                    assert(cost as int + best as int <= 1_000_001_000) by (nonlinear_arith)
                        requires
                            0 <= cost as int <= 1000,
                            0 <= best as int <= 1_000_000_000,
                    {};
                    assert(cost + best >= 0);
                    assert(cost + best <= 1_000_001_000);
                }
                let value = cost + best;
                let ghost before = dp_cur@;
                dp_cur.push(value);
                proof {
                    assert(matches as int == Self::col_count_prefix(grid@, col as int, v as int, m as int));
                    Self::lemma_col_count_prefix_bounds(grid@, col as int, v as int, m as int);
                    assert(cost as int == Self::col_cost(grid@, col as int, v as int));
                    Self::lemma_min_vec_prefix_eq_spec(dp_prev@, grid@, col as int, v as int, 10);
                    assert(best as int == Self::min_prev_prefix(grid@, col as int, v as int, 10));
                    assert(value as int == Self::min_cost_prefix_last(grid@, col as int + 1, v as int));
                    assert(dp_cur@ == before.push(value));
                    assert(0 <= value as int <= (col as int + 1) * (m as int));
                }
                v = v + 1;
            }
            dp_prev = dp_cur;
            col = col + 1;
        }

        let mut answer: i64 = 1_000_000_000;
        v = 0;
        while v < 10
            invariant
                m == grid.len(),
                n == grid[0].len(),
                1 <= m <= 1000,
                1 <= n <= 1000,
                col == n,
                dp_prev.len() == 10,
                0 <= v <= 10,
                answer as int == Self::min_vec_all_prefix(dp_prev@, v as int),
                forall |t: int| 0 <= t < 10 ==> #[trigger] dp_prev[t] as int == Self::min_cost_prefix_last(grid@, n as int, t),
                forall |t: int| 0 <= t < 10 ==> 0 <= #[trigger] dp_prev[t] as int <= (n as int) * (m as int),
            decreases 10 - v,
        {
            if dp_prev[v] < answer {
                answer = dp_prev[v];
            }
            proof {
                let old = Self::min_vec_all_prefix(dp_prev@, v as int);
                let cur = dp_prev@[v as int] as int;
                assert(Self::min_vec_all_prefix(dp_prev@, v as int + 1)
                    == if cur <= old { cur } else { old });
            }
            v = v + 1;
        }

        proof {
            Self::lemma_min_vec_all_prefix_eq_spec(dp_prev@, grid@, n as int, 10);
            Self::lemma_min_vec_all_prefix_nonneg(dp_prev@, 10);
            Self::lemma_min_vec_all_prefix_le_entry(dp_prev@, 10, 0);
            assert(answer as int == Self::min_total_prefix(grid@, n as int, 10));
            assert(answer as int == Self::min_operations_spec(grid@));
            assert(0 <= answer as int);
            assert(answer as int <= dp_prev[0] as int);
            assert(dp_prev[0] as int <= (n as int) * (m as int));
            assert((n as int) * (m as int) <= 1_000_000) by (nonlinear_arith)
                requires
                    1 <= n as int <= 1000,
                    1 <= m as int <= 1000,
            {};
            assert(answer as int <= 1_000_000);
            assert(answer as int <= i32::MAX);
            assert((answer as i32) as int == answer as int);
        }

        answer as i32
    }
}

}

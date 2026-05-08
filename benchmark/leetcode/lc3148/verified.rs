use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rows(grid: Seq<Vec<i32>>) -> int {
        grid.len() as int
    }

    pub open spec fn cols(grid: Seq<Vec<i32>>) -> int {
        grid[0].len() as int
    }

    pub open spec fn target_row(grid: Seq<Vec<i32>>, target: int) -> int {
        target / Self::cols(grid)
    }

    pub open spec fn target_col(grid: Seq<Vec<i32>>, target: int) -> int {
        target % Self::cols(grid)
    }

    pub open spec fn start_row_for_target(grid: Seq<Vec<i32>>, target: int, start: int) -> int {
        start / (Self::target_col(grid, target) + 1)
    }

    pub open spec fn start_col_for_target(grid: Seq<Vec<i32>>, target: int, start: int) -> int {
        start % (Self::target_col(grid, target) + 1)
    }

    pub open spec fn valid_path_pair(
        grid: Seq<Vec<i32>>,
        sr: int,
        sc: int,
        tr: int,
        tc: int,
    ) -> bool {
        &&& 0 <= sr <= tr < Self::rows(grid)
        &&& 0 <= sc <= tc < Self::cols(grid)
        &&& sr < tr || sc < tc
    }

    pub open spec fn path_score(
        grid: Seq<Vec<i32>>,
        sr: int,
        sc: int,
        tr: int,
        tc: int,
    ) -> int {
        grid[tr][tc] as int - grid[sr][sc] as int
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b {
            a
        } else {
            b
        }
    }

    pub open spec fn best_starts_for_target(
        grid: Seq<Vec<i32>>,
        target: int,
        start: int,
    ) -> int
        decreases
            (Self::target_row(grid, target) + 1)
                * (Self::target_col(grid, target) + 1) - start,
    {
        let tr = Self::target_row(grid, target);
        let tc = Self::target_col(grid, target);
        let limit = (tr + 1) * (tc + 1);
        if start >= limit {
            -100000int
        } else {
            let sr = Self::start_row_for_target(grid, target, start);
            let sc = Self::start_col_for_target(grid, target, start);
            let rest = Self::best_starts_for_target(grid, target, start + 1);
            if sr == tr && sc == tc {
                rest
            } else {
                Self::spec_max(Self::path_score(grid, sr, sc, tr, tc), rest)
            }
        }
    }

    pub open spec fn best_targets_from(grid: Seq<Vec<i32>>, target: int) -> int
        decreases Self::rows(grid) * Self::cols(grid) - target,
    {
        let total = Self::rows(grid) * Self::cols(grid);
        if target >= total {
            -100000int
        } else {
            Self::spec_max(
                Self::best_starts_for_target(grid, target, 0),
                Self::best_targets_from(grid, target + 1),
            )
        }
    }

    pub open spec fn best_path_score(grid: Seq<Vec<i32>>) -> int {
        Self::best_targets_from(grid, 0)
    }

    pub open spec fn max_score_spec(grid: Seq<Vec<i32>>, result: int) -> bool {
        &&& 2 <= grid.len() <= 1000
        &&& 2 <= grid[0].len() <= 1000
        &&& 4 <= grid.len() * grid[0].len() <= 100000
        &&& forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len()
        &&& forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid[i][j] <= 100000
        &&& result == Self::best_path_score(grid)
    }

    proof fn lemma_score_bounds(grid: Seq<Vec<i32>>, sr: int, sc: int, tr: int, tc: int)
        requires
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid[i][j] <= 100000,
            Self::valid_path_pair(grid, sr, sc, tr, tc),
        ensures
            -99999 <= Self::path_score(grid, sr, sc, tr, tc) <= 99999,
    {
        assert(0 <= tr < grid.len());
        assert(0 <= sr < grid.len());
        assert(grid[tr].len() == grid[0].len());
        assert(grid[sr].len() == grid[0].len());
        assert(0 <= tc < grid[tr].len());
        assert(0 <= sc < grid[sr].len());
        assert(1 <= grid[tr][tc] <= 100000);
        assert(1 <= grid[sr][sc] <= 100000);
        assert(grid[tr][tc] as int - grid[sr][sc] as int <= 99999);
        assert(grid[tr][tc] as int - grid[sr][sc] as int >= -99999);
    }

    fn spec_max_exec(a: i32, b: i32) -> (res: i32)
        ensures
            res as int == Self::spec_max(a as int, b as int),
            a <= res,
            b <= res,
            res == a || res == b,
    {
        if a >= b {
            a
        } else {
            b
        }
    }

    fn best_starts_for_target_exec(
        grid: &Vec<Vec<i32>>,
        target: usize,
        start: usize,
    ) -> (res: i32)
        requires
            2 <= grid.len() <= 1000,
            2 <= grid[0].len() <= 1000,
            4 <= grid.len() * grid[0].len() <= 100000,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid[i][j] <= 100000,
            target < grid.len() * grid[0].len(),
            start <= grid.len() * grid[0].len(),
        ensures
            res as int == Self::best_starts_for_target(grid@, target as int, start as int),
            -100000 <= res <= 100000,
        decreases grid.len() * grid[0].len() - start,
    {
        let n = grid[0].len();
        assert(n >= 2);
        assert(target < grid.len() * n);
        assert(target / n < grid.len()) by (nonlinear_arith)
            requires 0 <= target, target < grid.len() * n, 1 <= n;
        assert(target % n < n) by (nonlinear_arith)
            requires 0 <= target, 1 <= n;
        let tr = target / n;
        let tc = target % n;
        proof {
            lemma_fundamental_div_mod(target as int, n as int);
        }
        assert(target as int == ((target as int) / (n as int)) * (n as int) + (target as int) % (n as int));
        assert(0 <= (target as int) % (n as int) < n as int);
        assert(tr < grid.len());
        assert(tc < n);
        assert(tr + 1 <= grid.len());
        assert(tc + 1 <= n);
        assert((tr + 1) * (tc + 1) <= grid.len() * n) by (nonlinear_arith)
            requires tr + 1 <= grid.len(), tc + 1 <= n;
        assert((tr + 1) * (tc + 1) <= 100000);
        let limit = (tr + 1) * (tc + 1);
        if start >= limit {
            -100000
        } else {
            assert(start < grid.len() * n);
            assert(start + 1 <= grid.len() * n);
            assert(grid.len() * n - (start + 1) < grid.len() * n - start);
            let sr = start / (tc + 1);
            let sc = start % (tc + 1);
            proof {
                lemma_fundamental_div_mod(start as int, (tc + 1) as int);
            }
            assert(start as int == ((start as int) / ((tc + 1) as int)) * ((tc + 1) as int)
                + (start as int) % ((tc + 1) as int));
            assert(0 <= (start as int) % ((tc + 1) as int) < (tc + 1) as int);
            assert(sr <= tr) by (nonlinear_arith)
                requires
                    start < (tr + 1) * (tc + 1),
                    start as int == (sr as int) * ((tc + 1) as int) + (sc as int),
                    0 <= sc < tc + 1,
                    1 <= tc + 1;
            assert(sc <= tc);
            let rest = Self::best_starts_for_target_exec(grid, target, start + 1);
            assert(n as int == Self::cols(grid@));
            assert(tr as int == Self::target_row(grid@, target as int));
            assert(tc as int == Self::target_col(grid@, target as int));
            assert(sr as int == Self::start_row_for_target(grid@, target as int, start as int));
            assert(sc as int == Self::start_col_for_target(grid@, target as int, start as int));
            if sr == tr && sc == tc {
                rest
            } else {
                assert(0 <= sr <= tr < grid.len());
                assert(0 <= sc <= tc < n);
                assert(grid[sr as int].len() == n);
                assert(sr < tr || sc < tc);
                proof {
                    Self::lemma_score_bounds(grid@, sr as int, sc as int, tr as int, tc as int);
                }
                let score = grid[tr][tc] - grid[sr][sc];
                assert(score as int == Self::path_score(grid@, sr as int, sc as int, tr as int, tc as int));
                Self::spec_max_exec(score, rest)
            }
        }
    }

    fn best_targets_from_exec(grid: &Vec<Vec<i32>>, target: usize) -> (res: i32)
        requires
            2 <= grid.len() <= 1000,
            2 <= grid[0].len() <= 1000,
            4 <= grid.len() * grid[0].len() <= 100000,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid[i][j] <= 100000,
            target <= grid.len() * grid[0].len(),
        ensures
            res as int == Self::best_targets_from(grid@, target as int),
            -100000 <= res <= 100000,
        decreases grid.len() * grid[0].len() - target,
    {
        let total = grid.len() * grid[0].len();
        if target >= total {
            -100000
        } else {
            let here = Self::best_starts_for_target_exec(grid, target, 0);
            let rest = Self::best_targets_from_exec(grid, target + 1);
            assert(total as int == Self::rows(grid@) * Self::cols(grid@));
            Self::spec_max_exec(here, rest)
        }
    }

    pub fn max_score(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= grid.len() <= 1000,
            2 <= grid[0].len() <= 1000,
            4 <= grid.len() * grid[0].len() <= 100000,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid[i][j] <= 100000,
        ensures
            Self::max_score_spec(grid@, result as int),
    {
        Self::best_targets_from_exec(&grid, 0)
    }
}

}

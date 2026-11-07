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
}

pub open spec fn imin(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn min_prefix(grid: Seq<Vec<i32>>, i: int, j: int) -> int
    decreases i + j, 0int when i >= 0 && j >= 0
{
    if i < 0 || j < 0 {
        0
    } else if i == 0 && j == 0 {
        grid[0][0] as int
    } else if i == 0 {
        imin(grid[0][j] as int, min_prefix(grid, 0, j - 1))
    } else if j == 0 {
        imin(grid[i][0] as int, min_prefix(grid, i - 1, 0))
    } else {
        imin(grid[i][j] as int, imin(min_prefix(grid, i - 1, j), min_prefix(grid, i, j - 1)))
    }
}

pub open spec fn min_prefix_excl(grid: Seq<Vec<i32>>, i: int, j: int) -> int {
    if i == 0 && j == 0 {
        100001
    } else if i == 0 {
        min_prefix(grid, 0, j - 1)
    } else if j == 0 {
        min_prefix(grid, i - 1, 0)
    } else {
        imin(min_prefix(grid, i - 1, j), min_prefix(grid, i, j - 1))
    }
}

pub open spec fn best_cell(grid: Seq<Vec<i32>>, i: int, j: int) -> int {
    if i == 0 && j == 0 {
        -100000
    } else {
        grid[i][j] as int - min_prefix_excl(grid, i, j)
    }
}

impl Solution {
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
        let tr = target / n;
        let tc = target % n;
        let limit = (tr + 1) * (tc + 1);
        if start >= limit {
            -100000
        } else {
            let sr = start / (tc + 1);
            let sc = start % (tc + 1);
            let rest = Self::best_starts_for_target_exec(grid, target, start + 1);
            if sr == tr && sc == tc {
                rest
            } else {
                let score = grid[tr][tc] - grid[sr][sc];
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
        let rows: usize = grid.len();
        let cols: usize = grid[0].len();

        let mut minv: Vec<Vec<i32>> = Vec::new();
        let mut ans: i32 = -100000;

        let mut r: usize = 0;
        while r < rows {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols {
                let gv: i32 = grid[r][c];
                let mval: i32;
                if r == 0 && c == 0 {
                    mval = gv;
                } else if r == 0 {
                    let left = row[c - 1];
                    mval = if gv <= left { gv } else { left };
                } else if c == 0 {
                    let up = minv[r - 1][0];
                    mval = if gv <= up { gv } else { up };
                } else {
                    let up = minv[r - 1][c];
                    let left = row[c - 1];
                    let m1 = if gv <= up { gv } else { up };
                    mval = if m1 <= left { m1 } else { left };
                }
                row.push(mval);

                let excl: i32;
                if r == 0 && c == 0 {
                    excl = 100001;
                } else if r == 0 {
                    excl = row[c - 1];
                } else if c == 0 {
                    excl = minv[r - 1][0];
                } else {
                    let up2 = minv[r - 1][c];
                    let left2 = row[c - 1];
                    excl = if up2 <= left2 { up2 } else { left2 };
                }

                let best: i32;
                if r == 0 && c == 0 {
                    best = -100000;
                } else {
                    best = gv - excl;
                }

                if best > ans {
                    ans = best;
                }
                c += 1;
            }
            minv.push(row);
            r += 1;
        }

        ans
    }
}

}

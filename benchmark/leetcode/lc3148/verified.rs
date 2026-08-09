use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::arithmetic::div_mod::lemma_multiply_divide_lt;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse;

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

proof fn lemma_min_prefix_char(grid: Seq<Vec<i32>>, i: int, j: int)
    requires
        0 <= i < grid.len(),
        0 <= j < grid[0].len(),
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    ensures
        exists |r: int, c: int| 0 <= r <= i && 0 <= c <= j && min_prefix(grid, i, j) == grid[r][c] as int,
        forall |r: int, c: int| 0 <= r <= i && 0 <= c <= j ==> min_prefix(grid, i, j) <= #[trigger] grid[r][c] as int,
    decreases i + j,
{
    if i == 0 && j == 0 {
        assert(min_prefix(grid, 0, 0) == grid[0][0] as int);
    } else if i == 0 {
        lemma_min_prefix_char(grid, 0, j - 1);
        assert forall |r: int, c: int| 0 <= r <= 0 && 0 <= c <= j implies min_prefix(grid, 0, j) <= #[trigger] grid[r][c] as int by {
            if c < j {
                assert(min_prefix(grid, 0, j - 1) <= grid[r][c] as int);
            }
        }
    } else if j == 0 {
        lemma_min_prefix_char(grid, i - 1, 0);
        assert forall |r: int, c: int| 0 <= r <= i && 0 <= c <= 0 implies min_prefix(grid, i, 0) <= #[trigger] grid[r][c] as int by {
            if r < i {
                assert(min_prefix(grid, i - 1, 0) <= grid[r][c] as int);
            }
        }
    } else {
        lemma_min_prefix_char(grid, i - 1, j);
        lemma_min_prefix_char(grid, i, j - 1);
        assert forall |r: int, c: int| 0 <= r <= i && 0 <= c <= j implies min_prefix(grid, i, j) <= #[trigger] grid[r][c] as int by {
            if r == i && c == j {
            } else if r < i {
                assert(min_prefix(grid, i - 1, j) <= grid[r][c] as int);
            } else {
                assert(min_prefix(grid, i, j - 1) <= grid[r][c] as int);
            }
        }
    }
}

proof fn lemma_min_prefix_excl_char(grid: Seq<Vec<i32>>, i: int, j: int)
    requires
        0 <= i < grid.len(),
        0 <= j < grid[0].len(),
        !(i == 0 && j == 0),
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    ensures
        exists |r: int, c: int| 0 <= r <= i && 0 <= c <= j && !(r == i && c == j)
            && min_prefix_excl(grid, i, j) == grid[r][c] as int,
        forall |r: int, c: int| 0 <= r <= i && 0 <= c <= j && !(r == i && c == j) ==>
            min_prefix_excl(grid, i, j) <= #[trigger] grid[r][c] as int,
{
    if i == 0 {
        lemma_min_prefix_char(grid, 0, j - 1);
        assert forall |r: int, c: int| 0 <= r <= 0 && 0 <= c <= j && !(r == 0 && c == j) implies
            min_prefix_excl(grid, 0, j) <= #[trigger] grid[r][c] as int by {
            assert(c <= j - 1);
        }
    } else if j == 0 {
        lemma_min_prefix_char(grid, i - 1, 0);
        assert forall |r: int, c: int| 0 <= r <= i && 0 <= c <= 0 && !(r == i && c == 0) implies
            min_prefix_excl(grid, i, 0) <= #[trigger] grid[r][c] as int by {
            assert(r <= i - 1);
        }
    } else {
        lemma_min_prefix_char(grid, i - 1, j);
        lemma_min_prefix_char(grid, i, j - 1);
        assert forall |r: int, c: int| 0 <= r <= i && 0 <= c <= j && !(r == i && c == j) implies
            min_prefix_excl(grid, i, j) <= #[trigger] grid[r][c] as int by {
            if r < i {
                assert(min_prefix(grid, i - 1, j) <= grid[r][c] as int);
            } else {
                assert(min_prefix(grid, i, j - 1) <= grid[r][c] as int);
            }
        }
    }
}

pub open spec fn min_over_starts(grid: Seq<Vec<i32>>, target: int, start: int) -> int
    decreases
        (Solution::target_row(grid, target) + 1)
            * (Solution::target_col(grid, target) + 1) - start,
{
    let tr = Solution::target_row(grid, target);
    let tc = Solution::target_col(grid, target);
    let limit = (tr + 1) * (tc + 1);
    if start >= limit {
        100001int
    } else {
        let sr = Solution::start_row_for_target(grid, target, start);
        let sc = Solution::start_col_for_target(grid, target, start);
        let rest = min_over_starts(grid, target, start + 1);
        if sr == tr && sc == tc {
            rest
        } else {
            imin(grid[sr][sc] as int, rest)
        }
    }
}

proof fn lemma_best_starts_via_min(grid: Seq<Vec<i32>>, target: int, start: int)
    requires
        0 <= Solution::target_row(grid, target) < grid.len(),
        0 <= Solution::target_col(grid, target) < grid[0].len(),
        0 <= start,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100000,
    ensures
        ({
            let tr = Solution::target_row(grid, target);
            let tc = Solution::target_col(grid, target);
            let mv = min_over_starts(grid, target, start);
            (mv == 100001int ==> Solution::best_starts_for_target(grid, target, start) == -100000int)
            && (mv != 100001int ==>
                Solution::best_starts_for_target(grid, target, start)
                    == grid[tr][tc] as int - mv)
        }),
    decreases
        (Solution::target_row(grid, target) + 1)
            * (Solution::target_col(grid, target) + 1) - start,
{
    let tr = Solution::target_row(grid, target);
    let tc = Solution::target_col(grid, target);
    let limit = (tr + 1) * (tc + 1);
    if start < limit {
        lemma_best_starts_via_min(grid, target, start + 1);
        let sr = Solution::start_row_for_target(grid, target, start);
        let sc = Solution::start_col_for_target(grid, target, start);
        assert(start < (tc + 1) * (tr + 1)) by (nonlinear_arith)
            requires start < (tr + 1) * (tc + 1);
        lemma_multiply_divide_lt(start, tc + 1, tr + 1);
        assert(sr == start / (tc + 1));
        assert(sr < tr + 1);
        assert(0 <= sr <= tr);
        assert(0 <= sc <= tc) by {
            assert(0 <= start);
            assert(0 < tc + 1);
        }
        assert(sr < grid.len());
        assert(sc < grid[sr].len());
        let rest_mv = min_over_starts(grid, target, start + 1);
        let rest_best = Solution::best_starts_for_target(grid, target, start + 1);
        if sr == tr && sc == tc {
            assert(min_over_starts(grid, target, start) == rest_mv);
            assert(Solution::best_starts_for_target(grid, target, start) == rest_best);
        } else {
            let ps = Solution::path_score(grid, sr, sc, tr, tc);
            assert(ps == grid[tr][tc] as int - grid[sr][sc] as int);
            assert(Solution::best_starts_for_target(grid, target, start)
                == Solution::spec_max(ps, rest_best));
            let mv = min_over_starts(grid, target, start);
            assert(mv == imin(grid[sr][sc] as int, rest_mv));
            if rest_mv == 100001int {
                assert(rest_best == -100000int);
                assert(mv == grid[sr][sc] as int);
                assert(Solution::spec_max(ps, rest_best) == ps);
                assert(Solution::best_starts_for_target(grid, target, start) == grid[tr][tc] as int - mv);
            } else {
                assert(rest_best == grid[tr][tc] as int - rest_mv);
                if grid[sr][sc] as int <= rest_mv {
                    assert(mv == grid[sr][sc] as int);
                    assert(ps >= rest_best);
                    assert(Solution::spec_max(ps, rest_best) == ps);
                } else {
                    assert(mv == rest_mv);
                    assert(ps <= rest_best);
                    assert(Solution::spec_max(ps, rest_best) == rest_best);
                }
                assert(Solution::best_starts_for_target(grid, target, start) == grid[tr][tc] as int - mv);
            }
        }
    }
}

proof fn lemma_min_over_starts_ge_via_s(grid: Seq<Vec<i32>>, target: int, start: int, s: int)
    requires
        0 <= Solution::target_row(grid, target),
        0 <= Solution::target_col(grid, target),
        0 <= start <= s,
        s < (Solution::target_row(grid, target) + 1) * (Solution::target_col(grid, target) + 1),
        !(Solution::start_row_for_target(grid, target, s) == Solution::target_row(grid, target)
            && Solution::start_col_for_target(grid, target, s) == Solution::target_col(grid, target)),
        0 <= Solution::start_row_for_target(grid, target, s) < grid.len(),
        0 <= Solution::start_col_for_target(grid, target, s) < grid[Solution::start_row_for_target(grid, target, s)].len(),
    ensures
        min_over_starts(grid, target, start)
            <= grid[Solution::start_row_for_target(grid, target, s)][Solution::start_col_for_target(grid, target, s)] as int,
    decreases s - start,
{
    let tr = Solution::target_row(grid, target);
    let tc = Solution::target_col(grid, target);
    let sr = Solution::start_row_for_target(grid, target, s);
    let sc = Solution::start_col_for_target(grid, target, s);
    if start == s {
        let rest = min_over_starts(grid, target, start + 1);
        assert(min_over_starts(grid, target, start) == imin(grid[sr][sc] as int, rest));
    } else {
        lemma_min_over_starts_ge_via_s(grid, target, start + 1, s);
        let sr0 = Solution::start_row_for_target(grid, target, start);
        let sc0 = Solution::start_col_for_target(grid, target, start);
        let rest = min_over_starts(grid, target, start + 1);
        if sr0 == tr && sc0 == tc {
            assert(min_over_starts(grid, target, start) == rest);
        } else {
            assert(min_over_starts(grid, target, start) == imin(grid[sr0][sc0] as int, rest));
        }
    }
}

proof fn lemma_min_over_starts_achieved(grid: Seq<Vec<i32>>, target: int, start: int)
    requires
        0 <= Solution::target_row(grid, target) < grid.len(),
        0 <= Solution::target_col(grid, target) < grid[0].len(),
        0 <= start,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    ensures
        ({
            let tr = Solution::target_row(grid, target);
            let tc = Solution::target_col(grid, target);
            let mv = min_over_starts(grid, target, start);
            mv == 100001int || (exists |s: int|
                start <= s < (tr + 1) * (tc + 1)
                && !(Solution::start_row_for_target(grid, target, s) == tr
                    && Solution::start_col_for_target(grid, target, s) == tc)
                && mv == grid[Solution::start_row_for_target(grid, target, s)][Solution::start_col_for_target(grid, target, s)] as int)
        }),
    decreases
        (Solution::target_row(grid, target) + 1)
            * (Solution::target_col(grid, target) + 1) - start,
{
    let tr = Solution::target_row(grid, target);
    let tc = Solution::target_col(grid, target);
    let limit = (tr + 1) * (tc + 1);
    if start < limit {
        lemma_min_over_starts_achieved(grid, target, start + 1);
        let sr = Solution::start_row_for_target(grid, target, start);
        let sc = Solution::start_col_for_target(grid, target, start);
        let rest = min_over_starts(grid, target, start + 1);
        if sr == tr && sc == tc {
            assert(min_over_starts(grid, target, start) == rest);
        } else {
            let mv = min_over_starts(grid, target, start);
            assert(mv == imin(grid[sr][sc] as int, rest));
            if grid[sr][sc] as int <= rest {
                assert(mv == grid[sr][sc] as int);
            } else {
                assert(mv == rest);
            }
        }
    }
}

proof fn lemma_rc_to_s(grid: Seq<Vec<i32>>, target: int, r: int, c: int)
    requires
        0 <= Solution::target_row(grid, target),
        0 <= Solution::target_col(grid, target),
        0 <= r <= Solution::target_row(grid, target),
        0 <= c <= Solution::target_col(grid, target),
    ensures
        ({
            let tc = Solution::target_col(grid, target);
            let s = r * (tc + 1) + c;
            0 <= s < (Solution::target_row(grid, target) + 1) * (tc + 1)
                && Solution::start_row_for_target(grid, target, s) == r
                && Solution::start_col_for_target(grid, target, s) == c
        }),
{
    let tr = Solution::target_row(grid, target);
    let tc = Solution::target_col(grid, target);
    let s = r * (tc + 1) + c;
    assert(0 <= c < tc + 1);
    lemma_fundamental_div_mod_converse(s, tc + 1, r, c);
    assert(Solution::start_row_for_target(grid, target, s) == s / (tc + 1));
    assert(Solution::start_col_for_target(grid, target, s) == s % (tc + 1));
    assert(s <= tr * (tc + 1) + tc) by (nonlinear_arith)
        requires r <= tr, c <= tc, 0 <= tc, s == r * (tc + 1) + c;
    assert(tr * (tc + 1) + tc < (tr + 1) * (tc + 1)) by (nonlinear_arith);
}

proof fn lemma_min_over_starts_eq_min_prefix_excl(grid: Seq<Vec<i32>>, target: int)
    requires
        0 <= Solution::target_row(grid, target) < grid.len(),
        0 <= Solution::target_col(grid, target) < grid[0].len(),
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100000,
    ensures
        min_over_starts(grid, target, 0) == min_prefix_excl(grid, Solution::target_row(grid, target), Solution::target_col(grid, target)),
{
    let tr = Solution::target_row(grid, target);
    let tc = Solution::target_col(grid, target);
    let mv = min_over_starts(grid, target, 0);
    let me = min_prefix_excl(grid, tr, tc);
    if tr == 0 && tc == 0 {
        assert(mv == 100001int) by {
            let sr = Solution::start_row_for_target(grid, target, 0);
            let sc = Solution::start_col_for_target(grid, target, 0);
            assert(sr == tr && sc == tc);
            assert(mv == min_over_starts(grid, target, 1));
            assert((tr + 1) * (tc + 1) == 1) by (nonlinear_arith)
                requires tr == 0, tc == 0;
            assert(min_over_starts(grid, target, 1) == 100001int);
        }
    } else {
        lemma_min_prefix_excl_char(grid, tr, tc);
        lemma_min_over_starts_achieved(grid, target, 0);
        assert(mv <= me) by {
            let (r, c) = choose |r: int, c: int| 0 <= r <= tr && 0 <= c <= tc && !(r == tr && c == tc)
                && me == grid[r][c] as int;
            lemma_rc_to_s(grid, target, r, c);
            let s = r * (tc + 1) + c;
            lemma_min_over_starts_ge_via_s(grid, target, 0, s);
        }
        assert(me <= mv) by {
            if mv != 100001int {
                let s = choose |s: int| 0 <= s < (tr + 1) * (tc + 1)
                    && !(Solution::start_row_for_target(grid, target, s) == tr
                        && Solution::start_col_for_target(grid, target, s) == tc)
                    && mv == grid[Solution::start_row_for_target(grid, target, s)][Solution::start_col_for_target(grid, target, s)] as int;
                let r = Solution::start_row_for_target(grid, target, s);
                let c = Solution::start_col_for_target(grid, target, s);
                assert(0 <= s);
                assert(s < (tc + 1) * (tr + 1)) by (nonlinear_arith)
                    requires s < (tr + 1) * (tc + 1);
                lemma_multiply_divide_lt(s, tc + 1, tr + 1);
                assert(r == s / (tc + 1));
                assert(r < tr + 1);
                assert(0 <= r <= tr);
                assert(0 <= c <= tc);
            }
        }
    }
}

pub open spec fn best_cell(grid: Seq<Vec<i32>>, i: int, j: int) -> int {
    if i == 0 && j == 0 {
        -100000
    } else {
        grid[i][j] as int - min_prefix_excl(grid, i, j)
    }
}

proof fn lemma_best_starts_eq_best_cell(grid: Seq<Vec<i32>>, target: int)
    requires
        0 <= Solution::target_row(grid, target) < grid.len(),
        0 <= Solution::target_col(grid, target) < grid[0].len(),
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100000,
    ensures
        Solution::best_starts_for_target(grid, target, 0)
            == best_cell(grid, Solution::target_row(grid, target), Solution::target_col(grid, target)),
{
    let tr = Solution::target_row(grid, target);
    let tc = Solution::target_col(grid, target);
    lemma_best_starts_via_min(grid, target, 0);
    lemma_min_over_starts_eq_min_prefix_excl(grid, target);
    let mv = min_over_starts(grid, target, 0);
    if mv == 100001int {
        assert(tr == 0 && tc == 0) by {
            if !(tr == 0 && tc == 0) {
                lemma_min_prefix_excl_char(grid, tr, tc);
                assert(false);
            }
        }
    }
}

pub open spec fn best_cell_over_prefix(grid: Seq<Vec<i32>>, upto: int) -> int
    decreases upto,
{
    if upto <= 0 {
        -100000
    } else {
        Solution::spec_max(
            best_cell_over_prefix(grid, upto - 1),
            best_cell(grid, Solution::target_row(grid, upto - 1), Solution::target_col(grid, upto - 1)),
        )
    }
}

proof fn lemma_target_row_col_bounds(grid: Seq<Vec<i32>>, target: int)
    requires
        1 <= grid.len(),
        1 <= grid[0].len(),
        0 <= target < Solution::rows(grid) * Solution::cols(grid),
    ensures
        0 <= Solution::target_row(grid, target) < grid.len(),
        0 <= Solution::target_col(grid, target) < grid[0].len(),
{
    lemma_multiply_divide_lt(target, Solution::cols(grid), Solution::rows(grid));
}

proof fn lemma_best_cell_over_prefix_char(grid: Seq<Vec<i32>>, upto: int)
    requires
        1 <= grid.len(),
        1 <= grid[0].len(),
        0 <= upto <= Solution::rows(grid) * Solution::cols(grid),
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100000,
    ensures
        upto == 0 ==> best_cell_over_prefix(grid, upto) == -100000int,
        upto > 0 ==> (exists |t: int| 0 <= t < upto
            && best_cell_over_prefix(grid, upto) == best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t))),
        forall |t: int| 0 <= t < upto ==> best_cell_over_prefix(grid, upto)
            >= #[trigger] best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t)),
    decreases upto,
{
    if upto > 0 {
        lemma_best_cell_over_prefix_char(grid, upto - 1);
        lemma_target_row_col_bounds(grid, upto - 1);
        let cand = best_cell(grid, Solution::target_row(grid, upto - 1), Solution::target_col(grid, upto - 1));
        let prev = best_cell_over_prefix(grid, upto - 1);
        assert(best_cell_over_prefix(grid, upto) == Solution::spec_max(prev, cand));
        assert forall |t: int| 0 <= t < upto implies best_cell_over_prefix(grid, upto)
            >= #[trigger] best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t)) by {
            if t < upto - 1 {
                assert(prev >= best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t)));
            }
        }
    }
}

proof fn lemma_best_targets_from_char(grid: Seq<Vec<i32>>, target: int)
    requires
        1 <= grid.len(),
        1 <= grid[0].len(),
        0 <= target <= Solution::rows(grid) * Solution::cols(grid),
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100000,
    ensures
        target == Solution::rows(grid) * Solution::cols(grid) ==> Solution::best_targets_from(grid, target) == -100000int,
        target < Solution::rows(grid) * Solution::cols(grid) ==> (exists |t: int|
            target <= t < Solution::rows(grid) * Solution::cols(grid)
            && Solution::best_targets_from(grid, target) == best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t))),
        forall |t: int| target <= t < Solution::rows(grid) * Solution::cols(grid) ==>
            Solution::best_targets_from(grid, target) >= #[trigger] best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t)),
    decreases Solution::rows(grid) * Solution::cols(grid) - target,
{
    let total = Solution::rows(grid) * Solution::cols(grid);
    if target < total {
        lemma_best_targets_from_char(grid, target + 1);
        lemma_target_row_col_bounds(grid, target);
        lemma_best_starts_eq_best_cell(grid, target);
        let here = best_cell(grid, Solution::target_row(grid, target), Solution::target_col(grid, target));
        let rest = Solution::best_targets_from(grid, target + 1);
        assert(Solution::best_targets_from(grid, target) == Solution::spec_max(here, rest));
        assert forall |t: int| target <= t < total implies
            Solution::best_targets_from(grid, target) >= #[trigger] best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t)) by {
            if t > target {
                assert(rest >= best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t)));
            }
        }
    }
}

proof fn lemma_best_path_score_eq_prefix(grid: Seq<Vec<i32>>)
    requires
        1 <= grid.len(),
        1 <= grid[0].len(),
        1 <= Solution::rows(grid) * Solution::cols(grid),
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100000,
    ensures
        Solution::best_path_score(grid) == best_cell_over_prefix(grid, Solution::rows(grid) * Solution::cols(grid)),
{
    let total = Solution::rows(grid) * Solution::cols(grid);
    lemma_best_targets_from_char(grid, 0);
    lemma_best_cell_over_prefix_char(grid, total);
    let a = Solution::best_targets_from(grid, 0);
    let b = best_cell_over_prefix(grid, total);
    if total == 0 {
    } else {
        let t1 = choose |t: int| 0 <= t < total
            && a == best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t));
        assert(b >= best_cell(grid, Solution::target_row(grid, t1), Solution::target_col(grid, t1)));
        assert(b >= a);
        let t2 = choose |t: int| 0 <= t < total
            && b == best_cell(grid, Solution::target_row(grid, t), Solution::target_col(grid, t));
        assert(a >= best_cell(grid, Solution::target_row(grid, t2), Solution::target_col(grid, t2)));
        assert(a >= b);
    }
}

impl Solution {
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
        let rows: usize = grid.len();
        let cols: usize = grid[0].len();

        let mut minv: Vec<Vec<i32>> = Vec::new();
        let mut ans: i32 = -100000;

        let mut r: usize = 0;
        while r < rows
            invariant
                rows == grid.len(),
                cols == grid[0].len(),
                2 <= rows <= 1000,
                2 <= cols <= 1000,
                4 <= rows * cols <= 100000,
                forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid@[i].len() == cols as int,
                forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid@[i][j] <= 100000,
                r <= rows,
                minv.len() == r,
                forall |i: int| 0 <= i < r ==> #[trigger] minv[i].len() == cols as int,
                forall |i: int, j: int| 0 <= i < r && 0 <= j < cols as int ==>
                    #[trigger] minv[i][j] as int == min_prefix(grid@, i, j),
                ans as int == best_cell_over_prefix(grid@, r as int * cols as int),
            decreases rows - r,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols
                invariant
                    rows == grid.len(),
                    cols == grid[0].len(),
                    2 <= rows <= 1000,
                    2 <= cols <= 1000,
                    4 <= rows * cols <= 100000,
                    forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid@[i].len() == cols as int,
                    forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid@[i][j] <= 100000,
                    r < rows,
                    minv.len() == r,
                    forall |i: int| 0 <= i < r ==> #[trigger] minv[i].len() == cols as int,
                    forall |i: int, j: int| 0 <= i < r && 0 <= j < cols as int ==>
                        #[trigger] minv[i][j] as int == min_prefix(grid@, i, j),
                    c <= cols,
                    row.len() == c,
                    forall |j: int| 0 <= j < c ==> #[trigger] row[j] as int == min_prefix(grid@, r as int, j),
                    ans as int == best_cell_over_prefix(grid@, r as int * cols as int + c as int),
                decreases cols - c,
            {
                assert(r < grid.len());
                assert(grid[r as int].len() == cols as int);
                let gv: i32 = grid[r][c];
                let mval: i32;
                if r == 0 && c == 0 {
                    mval = gv;
                    proof {
                        assert(min_prefix(grid@, 0, 0) == grid@[0][0] as int);
                    }
                } else if r == 0 {
                    let left = row[c - 1];
                    mval = if gv <= left { gv } else { left };
                    proof {
                        assert(row[c as int - 1] as int == min_prefix(grid@, 0, c as int - 1));
                        assert(min_prefix(grid@, 0, c as int) == imin(grid@[0][c as int] as int, min_prefix(grid@, 0, c as int - 1)));
                    }
                } else if c == 0 {
                    assert(((r - 1) as int) < minv.len());
                    assert(minv[(r - 1) as int].len() == cols as int);
                    let up = minv[r - 1][0];
                    mval = if gv <= up { gv } else { up };
                    proof {
                        assert(minv[r as int - 1][0] as int == min_prefix(grid@, r as int - 1, 0));
                        assert(min_prefix(grid@, r as int, 0) == imin(grid@[r as int][0] as int, min_prefix(grid@, r as int - 1, 0)));
                    }
                } else {
                    assert(((r - 1) as int) < minv.len());
                    assert(minv[(r - 1) as int].len() == cols as int);
                    let up = minv[r - 1][c];
                    let left = row[c - 1];
                    let m1 = if gv <= up { gv } else { up };
                    mval = if m1 <= left { m1 } else { left };
                    proof {
                        assert(minv[r as int - 1][c as int] as int == min_prefix(grid@, r as int - 1, c as int));
                        assert(row[c as int - 1] as int == min_prefix(grid@, r as int, c as int - 1));
                        assert(min_prefix(grid@, r as int, c as int) == imin(grid@[r as int][c as int] as int,
                            imin(min_prefix(grid@, r as int - 1, c as int), min_prefix(grid@, r as int, c as int - 1))));
                    }
                }
                row.push(mval);

                let excl: i32;
                if r == 0 && c == 0 {
                    excl = 100001;
                } else if r == 0 {
                    excl = row[c - 1];
                    proof {
                        assert(row[c as int - 1] as int == min_prefix(grid@, 0, c as int - 1));
                        assert(min_prefix_excl(grid@, 0, c as int) == min_prefix(grid@, 0, c as int - 1));
                    }
                } else if c == 0 {
                    assert(((r - 1) as int) < minv.len());
                    assert(minv[(r - 1) as int].len() == cols as int);
                    excl = minv[r - 1][0];
                    proof {
                        assert(minv[r as int - 1][0] as int == min_prefix(grid@, r as int - 1, 0));
                        assert(min_prefix_excl(grid@, r as int, 0) == min_prefix(grid@, r as int - 1, 0));
                    }
                } else {
                    assert(((r - 1) as int) < minv.len());
                    assert(minv[(r - 1) as int].len() == cols as int);
                    let up2 = minv[r - 1][c];
                    let left2 = row[c - 1];
                    excl = if up2 <= left2 { up2 } else { left2 };
                    proof {
                        assert(minv[r as int - 1][c as int] as int == min_prefix(grid@, r as int - 1, c as int));
                        assert(row[c as int - 1] as int == min_prefix(grid@, r as int, c as int - 1));
                        assert(min_prefix_excl(grid@, r as int, c as int)
                            == imin(min_prefix(grid@, r as int - 1, c as int), min_prefix(grid@, r as int, c as int - 1)));
                    }
                }

                let best: i32;
                if r == 0 && c == 0 {
                    best = -100000;
                    proof {
                        assert(best_cell(grid@, 0, 0) == -100000int);
                    }
                } else {
                    proof {
                        lemma_min_prefix_excl_char(grid@, r as int, c as int);
                        let (wr, wc) = choose |wr: int, wc: int| 0 <= wr <= r as int && 0 <= wc <= c as int && !(wr == r as int && wc == c as int)
                            && min_prefix_excl(grid@, r as int, c as int) == grid@[wr][wc] as int;
                        assert(1 <= grid@[wr][wc] <= 100000);
                        assert(1 <= min_prefix_excl(grid@, r as int, c as int) <= 100000);
                    }
                    best = gv - excl;
                    proof {
                        assert(best_cell(grid@, r as int, c as int) == grid@[r as int][c as int] as int - min_prefix_excl(grid@, r as int, c as int));
                    }
                }

                let old_ans = ans;
                if best > ans {
                    ans = best;
                }
                proof {
                    assert(ans as int == Solution::spec_max(old_ans as int, best as int));
                    assert((r as int * cols as int + c as int) < (rows as int * cols as int)) by (nonlinear_arith)
                        requires (r as int) < (rows as int), (c as int) < (cols as int), (c as int) >= 0, (rows as int) >= 0, (cols as int) >= 0;
                    lemma_target_row_col_bounds(grid@, r as int * cols as int + c as int);
                    lemma_fundamental_div_mod_converse(r as int * cols as int + c as int, cols as int, r as int, c as int);
                    assert(Solution::target_row(grid@, r as int * cols as int + c as int) == r as int);
                    assert(Solution::target_col(grid@, r as int * cols as int + c as int) == c as int);
                    assert(best_cell_over_prefix(grid@, r as int * cols as int + c as int + 1)
                        == Solution::spec_max(
                            best_cell_over_prefix(grid@, r as int * cols as int + c as int),
                            best_cell(grid@, r as int, c as int)));
                }
                c += 1;
            }
            minv.push(row);
            r += 1;
            proof {
                assert((r as int - 1) * cols as int + cols as int == r as int * cols as int) by (nonlinear_arith)
                    requires cols as int >= 0;
            }
        }

        proof {
            lemma_best_path_score_eq_prefix(grid@);
            assert(rows as int * cols as int == grid@.len() * grid@[0].len());
            assert(ans as int == Self::best_path_score(grid@));
        }

        ans
    }
}

}

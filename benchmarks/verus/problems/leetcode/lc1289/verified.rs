use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_falling_path(path: Seq<int>, n: int) -> bool {
    path.len() == n
    && (forall |i: int| 0 <= i < n ==> 0 <= #[trigger] path[i] < n)
    && (forall |i: int| #![trigger path[i]] 0 <= i < n - 1 ==> path[i] != path[i + 1])
}

pub open spec fn path_sum(grid: Seq<Vec<i32>>, path: Seq<int>, k: int) -> int
    decreases k
{
    if k <= 0 { 0 }
    else { grid[k - 1][path[k - 1]] as int + path_sum(grid, path, k - 1) }
}

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn dp_val(grid: Seq<Vec<i32>>, row: int, col: int) -> int
        recommends 0 <= row < grid.len() as int, 0 <= col < grid.len() as int
        decreases grid.len() - row, 0nat
    {
        let n = grid.len() as int;
        if row >= n - 1 {
            grid[row][col] as int
        } else {
            grid[row][col] as int + Self::best_prev(grid, row + 1, col, n)
        }
    }

    pub open spec fn best_prev(grid: Seq<Vec<i32>>, row: int, excl: int, bound: int) -> int
        recommends 0 <= row < grid.len() as int
        decreases grid.len() - row, bound + 1
    {
        if bound <= 0 { i32::MAX as int }
        else if bound - 1 == excl { Self::best_prev(grid, row, excl, bound - 1) }
        else { Self::min2(Self::dp_val(grid, row, bound - 1), Self::best_prev(grid, row, excl, bound - 1)) }
    }

    pub open spec fn min_dp(grid: Seq<Vec<i32>>, row: int, bound: int) -> int
        recommends 0 <= row < grid.len() as int
        decreases grid.len() - row, bound + 1
    {
        if bound <= 0 { i32::MAX as int }
        else { Self::min2(Self::dp_val(grid, row, bound - 1), Self::min_dp(grid, row, bound - 1)) }
    }

    

    pub open spec fn opt_col_min_dp(grid: Seq<Vec<i32>>, row: int, bound: int) -> int
        decreases bound
    {
        if bound <= 1 { 0 }
        else if Self::dp_val(grid, row, bound - 1) <= Self::min_dp(grid, row, bound - 1) {
            bound - 1
        } else {
            Self::opt_col_min_dp(grid, row, bound - 1)
        }
    }

    pub open spec fn opt_col_best_prev(grid: Seq<Vec<i32>>, row: int, excl: int, bound: int) -> int
        decreases bound
    {
        if bound <= 0 { 0 }
        else if excl >= bound {
            Self::opt_col_min_dp(grid, row, bound)
        } else if bound - 1 == excl {
            Self::opt_col_best_prev(grid, row, excl, bound - 1)
        } else if Self::dp_val(grid, row, bound - 1) <= Self::best_prev(grid, row, excl, bound - 1) {
            bound - 1
        } else {
            Self::opt_col_best_prev(grid, row, excl, bound - 1)
        }
    }

    pub open spec fn opt_path_col(grid: Seq<Vec<i32>>, row: int) -> int
        decreases row
    {
        let n = grid.len() as int;
        if row <= 0 {
            Self::opt_col_min_dp(grid, 0, n)
        } else {
            Self::opt_col_best_prev(grid, row, Self::opt_path_col(grid, row - 1), n)
        }
    }

    

    proof fn lemma_best_prev_ge_min_dp(grid: Seq<Vec<i32>>, row: int, excl: int, bound: int)
        requires 0 <= excl, 0 <= row < grid.len() as int
        ensures Self::best_prev(grid, row, excl, bound) >= Self::min_dp(grid, row, bound)
        decreases grid.len() - row, bound + 1
    {
        if bound > 0 {
            Self::lemma_best_prev_ge_min_dp(grid, row, excl, bound - 1);
        }
    }

    proof fn lemma_best_prev_le_val(grid: Seq<Vec<i32>>, row: int, excl: int, bound: int, k: int)
        requires 0 <= k < bound, k != excl, 0 <= row < grid.len() as int
        ensures Self::best_prev(grid, row, excl, bound) <= Self::dp_val(grid, row, k)
        decreases grid.len() - row, bound + 1
    {
        if bound - 1 == excl {
            Self::lemma_best_prev_le_val(grid, row, excl, bound - 1, k);
        } else if bound - 1 == k {
        } else {
            Self::lemma_best_prev_le_val(grid, row, excl, bound - 1, k);
        }
    }

    proof fn lemma_dp_val_bounds(grid: Seq<Vec<i32>>, row: int, col: int)
        requires
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            forall |i: int, k: int| 0 <= i < grid.len() && 0 <= k < grid[i].len()
                ==> -99 <= #[trigger] grid[i][k] <= 99,
            0 <= row < grid.len() as int,
            0 <= col < grid.len() as int,
        ensures
            -99 * (grid.len() - row) <= Self::dp_val(grid, row, col) <= 99 * (grid.len() - row),
        decreases grid.len() - row, 0nat
    {
        let n = grid.len() as int;
        if row < n - 1 {
            let other: int = if col == 0 { 1 } else { 0 };
            Self::lemma_dp_val_bounds(grid, row + 1, other);
            Self::lemma_best_prev_le_val(grid, row + 1, col, n, other);
            assert forall |k: int| 0 <= k < n implies
                -99 * (n - (row + 1)) <= #[trigger] Self::dp_val(grid, row + 1, k)
                    <= 99 * (n - (row + 1)) by {
                Self::lemma_dp_val_bounds(grid, row + 1, k);
            }
            assert(99 * (n - (row + 1)) < i32::MAX as int) by (nonlinear_arith)
                requires 1 <= n <= 200, 0 <= row, row + 1 < n;
            Self::lemma_min_dp_bounds(grid, row + 1, n,
                -99 * (n - (row + 1)), 99 * (n - (row + 1)));
            Self::lemma_best_prev_ge_min_dp(grid, row + 1, col, n);
            assert(-99 * (n - row) <= Self::dp_val(grid, row, col)) by (nonlinear_arith)
                requires
                    Self::dp_val(grid, row, col) == grid[row][col] as int + Self::best_prev(grid, row + 1, col, n),
                    -99 <= grid[row][col] as int <= 99,
                    Self::best_prev(grid, row + 1, col, n) >= Self::min_dp(grid, row + 1, n),
                    Self::min_dp(grid, row + 1, n) >= -99 * (n - (row + 1)),
            {}
            assert(Self::dp_val(grid, row, col) <= 99 * (n - row)) by (nonlinear_arith)
                requires
                    Self::dp_val(grid, row, col) == grid[row][col] as int + Self::best_prev(grid, row + 1, col, n),
                    grid[row][col] as int <= 99,
                    Self::best_prev(grid, row + 1, col, n) <= Self::dp_val(grid, row + 1, other),
                    Self::dp_val(grid, row + 1, other) <= 99 * (n - (row + 1)),
            {}
        }
    }

    proof fn lemma_min_dp_bounds(grid: Seq<Vec<i32>>, row: int, bound: int, lo: int, hi: int)
        requires
            bound > 0,
            hi < i32::MAX as int,
            0 <= row < grid.len() as int,
            forall |k: int| 0 <= k < bound ==> lo <= #[trigger] Self::dp_val(grid, row, k) <= hi,
        ensures
            lo <= Self::min_dp(grid, row, bound) <= hi,
        decreases grid.len() - row, bound + 1
    {
        if bound == 1 {
            assert(Self::min_dp(grid, row, 0) == i32::MAX as int);
            assert(Self::dp_val(grid, row, 0) <= hi);
            assert(Self::dp_val(grid, row, 0) < i32::MAX as int);
        } else {
            Self::lemma_min_dp_bounds(grid, row, bound - 1, lo, hi);
        }
    }

    proof fn lemma_best_prev_bounds(grid: Seq<Vec<i32>>, row: int, excl: int, bound: int, lo: int, hi: int)
        requires
            bound >= 2,
            0 <= excl < bound,
            hi < i32::MAX as int,
            0 <= row < grid.len() as int,
            forall |k: int| 0 <= k < bound ==> lo <= #[trigger] Self::dp_val(grid, row, k) <= hi,
        ensures
            lo <= Self::best_prev(grid, row, excl, bound) <= hi,
    {
        let other: int = if excl == 0 { 1 } else { 0 };
        Self::lemma_best_prev_le_val(grid, row, excl, bound, other);
        Self::lemma_best_prev_ge_min_dp(grid, row, excl, bound);
        Self::lemma_min_dp_bounds(grid, row, bound, lo, hi);
    }

    proof fn lemma_excl_out_of_range(grid: Seq<Vec<i32>>, row: int, excl: int, bound: int)
        requires excl >= bound, 0 <= row < grid.len() as int
        ensures Self::best_prev(grid, row, excl, bound) == Self::min_dp(grid, row, bound)
        decreases grid.len() - row, bound + 1
    {
        if bound > 0 {
            Self::lemma_excl_out_of_range(grid, row, excl, bound - 1);
        }
    }

    

    proof fn lemma_opt_col_min_dp(grid: Seq<Vec<i32>>, row: int, bound: int)
        requires
            bound >= 1,
            0 <= row < grid.len() as int,
            bound <= grid.len() as int,
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            forall |i: int, k: int| 0 <= i < grid.len() && 0 <= k < grid[i].len()
                ==> -99 <= #[trigger] grid[i][k] <= 99,
        ensures
            0 <= Self::opt_col_min_dp(grid, row, bound) < bound,
            Self::dp_val(grid, row, Self::opt_col_min_dp(grid, row, bound))
                == Self::min_dp(grid, row, bound),
        decreases bound
    {
        if bound == 1 {
            Self::lemma_dp_val_bounds(grid, row, 0);
            assert(99 * (grid.len() - row) < i32::MAX as int) by (nonlinear_arith)
                requires 1 <= grid.len() as int <= 200, 0 <= row, row < grid.len() as int;
        } else {
            if !(Self::dp_val(grid, row, bound - 1) <= Self::min_dp(grid, row, bound - 1)) {
                Self::lemma_opt_col_min_dp(grid, row, bound - 1);
            }
        }
    }

    proof fn lemma_opt_col_best_prev(grid: Seq<Vec<i32>>, row: int, excl: int, bound: int)
        requires
            0 <= row < grid.len() as int,
            bound >= 1,
            bound <= grid.len() as int,
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            forall |i: int, k: int| 0 <= i < grid.len() && 0 <= k < grid[i].len()
                ==> -99 <= #[trigger] grid[i][k] <= 99,
            excl < 0 || excl >= bound || bound >= 2,
        ensures
            0 <= Self::opt_col_best_prev(grid, row, excl, bound) < bound,
            Self::opt_col_best_prev(grid, row, excl, bound) != excl,
            Self::dp_val(grid, row, Self::opt_col_best_prev(grid, row, excl, bound))
                == Self::best_prev(grid, row, excl, bound),
        decreases bound
    {
        if excl >= bound {
            Self::lemma_excl_out_of_range(grid, row, excl, bound);
            Self::lemma_opt_col_min_dp(grid, row, bound);
        } else if bound - 1 == excl {
            Self::lemma_opt_col_best_prev(grid, row, excl, bound - 1);
        } else {
            
            Self::lemma_dp_val_bounds(grid, row, bound - 1);
            assert(99 * (grid.len() - row) < i32::MAX as int) by (nonlinear_arith)
                requires 1 <= grid.len() as int <= 200, 0 <= row, row < grid.len() as int;
            if Self::dp_val(grid, row, bound - 1) <= Self::best_prev(grid, row, excl, bound - 1) {
            } else {
                
                assert(bound >= 2) by {
                    if bound == 1 {
                        assert(Self::best_prev(grid, row, excl, 0) == i32::MAX as int);
                    }
                }
                
                if bound == 2 && excl >= 0 {
                    
                    
                    assert(Self::best_prev(grid, row, excl, 0) == i32::MAX as int);
                    assert(Self::best_prev(grid, row, excl, bound - 1)
                        == Self::best_prev(grid, row, excl, 0));
                    
                    
                    assert(false);
                }
                Self::lemma_opt_col_best_prev(grid, row, excl, bound - 1);
            }
        }
    }

    

    proof fn lemma_min_dp_le_dp_val(grid: Seq<Vec<i32>>, row: int, col: int, bound: int)
        requires 0 <= col < bound, 0 <= row < grid.len() as int
        ensures Self::min_dp(grid, row, bound) <= Self::dp_val(grid, row, col)
        decreases bound
    {
        if bound - 1 != col {
            Self::lemma_min_dp_le_dp_val(grid, row, col, bound - 1);
        }
    }

    proof fn lemma_suffix_ge_dp_val(grid: Seq<Vec<i32>>, path: Seq<int>, row: int)
        requires
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            is_falling_path(path, grid.len() as int),
            0 <= row < grid.len() as int,
        ensures
            path_sum(grid, path, grid.len() as int) - path_sum(grid, path, row)
                >= Self::dp_val(grid, row, path[row])
        decreases grid.len() as int - row
    {
        let n = grid.len() as int;
        if row == n - 1 {
            assert(path_sum(grid, path, n) == grid[n-1][path[n-1]] as int + path_sum(grid, path, n-1));
        } else {
            Self::lemma_suffix_ge_dp_val(grid, path, row + 1);
            assert(path_sum(grid, path, (row + 1) as int)
                == grid[row][path[row]] as int + path_sum(grid, path, row));
            assert(path[row] != path[row + 1]);
            Self::lemma_best_prev_le_val(grid, row + 1, path[row], n, path[row + 1]);
        }
    }

    proof fn lemma_optimality(grid: Seq<Vec<i32>>, path: Seq<int>)
        requires
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            is_falling_path(path, grid.len() as int),
        ensures
            path_sum(grid, path, grid.len() as int) >= Self::min_dp(grid, 0, grid.len() as int)
    {
        let n = grid.len() as int;
        Self::lemma_suffix_ge_dp_val(grid, path, 0);
        assert(path_sum(grid, path, 0) == 0int);
        Self::lemma_min_dp_le_dp_val(grid, 0, path[0int], n);
    }

    

    proof fn lemma_opt_path_col_valid(grid: Seq<Vec<i32>>, row: int)
        requires
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            forall |i: int, k: int| 0 <= i < grid.len() && 0 <= k < grid[i].len()
                ==> -99 <= #[trigger] grid[i][k] <= 99,
            0 <= row < grid.len() as int,
        ensures
            0 <= Self::opt_path_col(grid, row) < grid.len() as int,
            row > 0 ==> Self::opt_path_col(grid, row) != Self::opt_path_col(grid, row - 1),
            Self::dp_val(grid, row, Self::opt_path_col(grid, row))
                == (if row == 0 { Self::min_dp(grid, 0, grid.len() as int) }
                    else { Self::best_prev(grid, row, Self::opt_path_col(grid, row - 1), grid.len() as int) }),
        decreases row
    {
        let n = grid.len() as int;
        if row <= 0 {
            Self::lemma_opt_col_min_dp(grid, 0, n);
        } else {
            Self::lemma_opt_path_col_valid(grid, row - 1);
            let prev = Self::opt_path_col(grid, row - 1);
            Self::lemma_opt_col_best_prev(grid, row, prev, n);
        }
    }

    proof fn lemma_opt_path_suffix(grid: Seq<Vec<i32>>, opt_path: Seq<int>, row: int)
        requires
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            forall |i: int, k: int| 0 <= i < grid.len() && 0 <= k < grid[i].len()
                ==> -99 <= #[trigger] grid[i][k] <= 99,
            0 <= row < grid.len() as int,
            opt_path.len() == grid.len() as int,
            forall |i: int| 0 <= i < grid.len() as int
                ==> opt_path[i] == Self::opt_path_col(grid, i),
        ensures
            path_sum(grid, opt_path, grid.len() as int) - path_sum(grid, opt_path, row)
                == Self::dp_val(grid, row, opt_path[row])
        decreases grid.len() as int - row
    {
        let n = grid.len() as int;
        if row == n - 1 {
            assert(path_sum(grid, opt_path, n) == grid[n-1][opt_path[n-1]] as int + path_sum(grid, opt_path, n-1));
        } else {
            Self::lemma_opt_path_suffix(grid, opt_path, row + 1);
            assert(path_sum(grid, opt_path, (row + 1) as int)
                == grid[row][opt_path[row]] as int + path_sum(grid, opt_path, row));
            Self::lemma_opt_path_col_valid(grid, row + 1);
        }
    }

    proof fn lemma_achievability(grid: Seq<Vec<i32>>)
        requires
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            forall |i: int, k: int| 0 <= i < grid.len() && 0 <= k < grid[i].len()
                ==> -99 <= #[trigger] grid[i][k] <= 99,
        ensures
            exists |path: Seq<int>| is_falling_path(path, grid.len() as int)
                && path_sum(grid, path, grid.len() as int) == Self::min_dp(grid, 0, grid.len() as int),
    {
        let n = grid.len() as int;
        let opt_path = Seq::new(n as nat, |row: int| Self::opt_path_col(grid, row));

        assert(opt_path.len() == n);

        assert forall |i: int| 0 <= i < n implies
            0 <= #[trigger] opt_path[i] < n by {
            Self::lemma_opt_path_col_valid(grid, i);
        }

        assert forall |i: int| #![trigger opt_path[i]] 0 <= i < n - 1 implies
            opt_path[i] != opt_path[i + 1] by {
            Self::lemma_opt_path_col_valid(grid, i + 1);
        }

        assert(is_falling_path(opt_path, n));

        Self::lemma_opt_path_suffix(grid, opt_path, 0);
        assert(path_sum(grid, opt_path, 0) == 0int);
        Self::lemma_opt_col_min_dp(grid, 0, n);
        assert(path_sum(grid, opt_path, n) == Self::min_dp(grid, 0, n));
    }

    

    pub fn min_falling_path_sum(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 200,
            forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len()
                ==> -99 <= #[trigger] grid[i][j] <= 99,
        ensures
            exists |path: Seq<int>| is_falling_path(path, grid.len() as int)
                && path_sum(grid@, path, grid.len() as int) == result as int,
            forall |path: Seq<int>| is_falling_path(path, grid.len() as int)
                ==> path_sum(grid@, path, grid.len() as int) >= result as int,
    {
        let n = grid.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k = 0usize;
        while k < n
            invariant
                n == grid.len(),
                1 <= n <= 200,
                forall |i: int| 0 <= i < n as int ==> (#[trigger] grid[i]).len() == n,
                dp@.len() == k as int,
                0 <= k <= n,
                forall |j: int| 0 <= j < k as int ==> (#[trigger] dp@[j]) == grid[n - 1 as int][j],
            decreases n - k
        {
            dp.push(grid[n - 1][k]);
            k = k + 1;
        }
        proof {
            assert forall |j: int| 0 <= j < n as int implies
                (#[trigger] dp@[j]) as int == Self::dp_val(grid@, (n - 1) as int, j) by {};
        }
        let mut row = n - 1;
        while row > 0
            invariant
                n == grid.len(),
                1 <= n <= 200,
                forall |i: int| 0 <= i < n as int ==> (#[trigger] grid[i]).len() == n,
                forall |i: int, j: int| 0 <= i < n as int && 0 <= j < grid[i].len()
                    ==> -99 <= #[trigger] grid[i][j] <= 99,
                dp@.len() == n as int,
                0 <= row < n,
                forall |j: int| 0 <= j < n as int ==>
                    (#[trigger] dp@[j]) as int == Self::dp_val(grid@, row as int, j),
                forall |j: int| 0 <= j < n as int ==>
                    -99 * (n as int - row as int) <= (#[trigger] dp@[j]) as int
                        <= 99 * (n as int - row as int),
            decreases row
        {
            row = row - 1;
            let ghost ni = n as int;
            let ghost ri = row as int;
            proof {
                assert(0 <= ri);
                assert(ri + 1 < ni);
            }

            let mut min1 = dp[0];
            let mut min1_idx: usize = 0;
            let mut min2 = i32::MAX;
            proof {
                assert(dp@[0int] as int == Self::dp_val(grid@, ri + 1, 0));
                Self::lemma_dp_val_bounds(grid@, ri + 1, 0);
                assert(99 * (ni - (ri + 1)) <= 19800) by (nonlinear_arith)
                    requires 1 <= ni <= 200, 0 <= ri;
                assert(Self::dp_val(grid@, ri + 1, 0) < i32::MAX as int);
                assert(Self::min_dp(grid@, ri + 1, 0) == i32::MAX as int);
                assert(Self::min_dp(grid@, ri + 1, 1)
                    == Self::min2(Self::dp_val(grid@, ri + 1, 0), i32::MAX as int));
                assert(min1 as int == Self::dp_val(grid@, ri + 1, 0));
                assert(min1 as int == Self::min_dp(grid@, ri + 1, 1));
                assert(Self::best_prev(grid@, ri + 1, 0, 0) == i32::MAX as int);
                assert(Self::best_prev(grid@, ri + 1, 0, 1)
                    == Self::best_prev(grid@, ri + 1, 0, 0));
                assert(min2 as int == i32::MAX as int);
                assert(min2 as int == Self::best_prev(grid@, ri + 1, 0, 1));
            }
            let mut k = 1usize;
            while k < n
                invariant
                    n == grid.len(), ni == n as int, ri == row as int,
                    1 <= n <= 200,
                    0 <= ri, ri + 1 < ni,
                    dp@.len() == ni,
                    1 <= k <= n,
                    0 <= min1_idx < k,
                    forall |j: int| 0 <= j < ni ==>
                        (#[trigger] dp@[j]) as int == Self::dp_val(grid@, ri + 1, j),
                    min1 as int == Self::min_dp(grid@, ri + 1, k as int),
                    Self::dp_val(grid@, ri + 1, min1_idx as int) == min1 as int,
                    min2 as int == Self::best_prev(grid@, ri + 1, min1_idx as int, k as int),
                    forall |j: int| 0 <= j < ni ==>
                        -99 * (ni - (ri + 1)) <= (#[trigger] dp@[j]) as int
                            <= 99 * (ni - (ri + 1)),
                decreases n - k
            {
                proof {
                    assert(dp@[k as int] as int == Self::dp_val(grid@, ri + 1, k as int));
                }
                if dp[k] < min1 {
                    min2 = min1;
                    min1 = dp[k];
                    min1_idx = k;
                    proof {
                        Self::lemma_excl_out_of_range(grid@, ri + 1, k as int, k as int);
                    }
                } else if dp[k] < min2 {
                    min2 = dp[k];
                }
                k = k + 1;
            }

            proof {
                assert forall |jj: int| 0 <= jj < ni implies
                    -99 * (ni - (ri + 1)) <= #[trigger] Self::dp_val(grid@, ri + 1, jj)
                        <= 99 * (ni - (ri + 1)) by {
                    Self::lemma_dp_val_bounds(grid@, ri + 1, jj);
                }
                assert(99 * (ni - (ri + 1)) < i32::MAX as int) by (nonlinear_arith)
                    requires 1 <= ni <= 200, 0 <= ri, ri + 1 < ni;
                Self::lemma_min_dp_bounds(grid@, ri + 1, ni,
                    -99 * (ni - (ri + 1)), 99 * (ni - (ri + 1)));
                assert(ni >= 2) by { assert(ri + 1 < ni); assert(ri >= 0); }
                Self::lemma_best_prev_bounds(grid@, ri + 1, min1_idx as int, ni,
                    -99 * (ni - (ri + 1)), 99 * (ni - (ri + 1)));
                assert(99 * (ni - (ri + 1)) <= 19800) by (nonlinear_arith)
                    requires 1 <= ni <= 200, 0 <= ri;
                assert(-19800 <= min1 as int <= 19800);
                assert(-19800 <= min2 as int <= 19800);
            }

            let mut j = 0usize;
            while j < n
                invariant
                    n == grid.len(), ni == n as int, ri == row as int,
                    1 <= n <= 200,
                    forall |i: int| 0 <= i < ni ==> (#[trigger] grid[i]).len() == n,
                    forall |i: int, jj: int| 0 <= i < ni && 0 <= jj < grid[i].len()
                        ==> -99 <= #[trigger] grid[i][jj] <= 99,
                    dp@.len() == ni,
                    0 <= j <= n,
                    0 <= ri, ri + 1 < ni,
                    0 <= min1_idx < n,
                    min1 as int == Self::min_dp(grid@, ri + 1, ni),
                    min2 as int == Self::best_prev(grid@, ri + 1, min1_idx as int, ni),
                    Self::dp_val(grid@, ri + 1, min1_idx as int) == min1 as int,
                    -19800 <= min1 as int <= 19800,
                    -19800 <= min2 as int <= 19800,
                    forall |k: int| 0 <= k < j as int ==>
                        (#[trigger] dp@[k]) as int == Self::dp_val(grid@, ri, k),
                    forall |k: int| j as int <= k < ni ==>
                        (#[trigger] dp@[k]) as int == Self::dp_val(grid@, ri + 1, k),
                    forall |k: int| 0 <= k < j as int ==>
                        -99 * (ni - ri) <= (#[trigger] dp@[k]) as int <= 99 * (ni - ri),
                    forall |k: int| j as int <= k < ni ==>
                        -99 * (ni - (ri + 1)) <= (#[trigger] dp@[k]) as int
                            <= 99 * (ni - (ri + 1)),
                decreases n - j
            {
                proof {
                    let ji = j as int;
                    assert(Self::dp_val(grid@, ri, ji)
                        == grid@[ri][ji] as int + Self::best_prev(grid@, ri + 1, ji, ni));
                    if ji == min1_idx as int {
                        assert(Self::best_prev(grid@, ri + 1, ji, ni) == min2 as int);
                    } else {
                        Self::lemma_best_prev_ge_min_dp(grid@, ri + 1, ji, ni);
                        Self::lemma_best_prev_le_val(grid@, ri + 1, ji, ni, min1_idx as int);
                        assert(Self::best_prev(grid@, ri + 1, ji, ni) >= min1 as int);
                        assert(Self::best_prev(grid@, ri + 1, ji, ni) <= min1 as int);
                        assert(Self::best_prev(grid@, ri + 1, ji, ni) == min1 as int);
                    }
                    assert(-99 <= grid@[ri][ji] <= 99);
                    assert(i32::MIN <= grid@[ri][ji] as int + min1 as int) by (nonlinear_arith)
                        requires -99 <= grid@[ri][ji] as int, -19800 <= min1 as int;
                    assert(grid@[ri][ji] as int + min1 as int <= i32::MAX) by (nonlinear_arith)
                        requires grid@[ri][ji] as int <= 99, min1 as int <= 19800;
                    assert(i32::MIN <= grid@[ri][ji] as int + min2 as int) by (nonlinear_arith)
                        requires -99 <= grid@[ri][ji] as int, -19800 <= min2 as int;
                    assert(grid@[ri][ji] as int + min2 as int <= i32::MAX) by (nonlinear_arith)
                        requires grid@[ri][ji] as int <= 99, min2 as int <= 19800;
                }
                if j == min1_idx {
                    dp.set(j, grid[row][j] + min2);
                } else {
                    dp.set(j, grid[row][j] + min1);
                }
                proof {
                    let ji = j as int;
                    assert(dp@[ji] as int == Self::dp_val(grid@, ri, ji));
                    assert forall |k: int| 0 <= k < ji + 1 implies
                        (#[trigger] dp@[k]) as int == Self::dp_val(grid@, ri, k) by {};
                    assert forall |k: int| ji + 1 <= k < ni implies
                        (#[trigger] dp@[k]) as int == Self::dp_val(grid@, ri + 1, k) by {};
                    assert forall |k: int| 0 <= k < ji + 1 implies
                        -99 * (ni - ri) <= (#[trigger] dp@[k]) as int <= 99 * (ni - ri) by {
                        if k == ji {
                            Self::lemma_dp_val_bounds(grid@, ri, k);
                        }
                    };
                }
                j = j + 1;
            }
        }

        let mut result = dp[0];
        proof {
            assert(dp@[0int] as int == Self::dp_val(grid@, 0, 0));
            Self::lemma_dp_val_bounds(grid@, 0, 0);
            assert(99 * (n as int) <= 19800) by (nonlinear_arith)
                requires 1 <= n as int <= 200;
            assert(Self::dp_val(grid@, 0, 0) < i32::MAX as int);
            assert(Self::min_dp(grid@, 0, 0) == i32::MAX as int);
            assert(Self::min_dp(grid@, 0, 1)
                == Self::min2(Self::dp_val(grid@, 0, 0), i32::MAX as int));
            assert(Self::min_dp(grid@, 0, 1) == Self::dp_val(grid@, 0, 0));
            assert(result as int == Self::dp_val(grid@, 0, 0));
            assert(result as int == Self::min_dp(grid@, 0, 1));
        }
        let mut k = 1usize;
        while k < n
            invariant
                n == grid.len(),
                dp@.len() == n as int,
                1 <= k <= n,
                forall |j: int| 0 <= j < n as int ==>
                    (#[trigger] dp@[j]) as int == Self::dp_val(grid@, 0, j),
                result as int == Self::min_dp(grid@, 0, k as int),
            decreases n - k
        {
            proof {
                assert(dp@[k as int] as int == Self::dp_val(grid@, 0, k as int));
            }
            if dp[k] < result {
                result = dp[k];
            }
            k = k + 1;
        }

        
        proof {
            Self::lemma_achievability(grid@);

            assert forall |path: Seq<int>| is_falling_path(path, grid.len() as int)
                implies path_sum(grid@, path, grid.len() as int) >= result as int by {
                Self::lemma_optimality(grid@, path);
            }
        }

        result
    }
}

}

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
        while k < n {
            dp.push(grid[n - 1][k]);
            k = k + 1;
        }
        let mut row = n - 1;
        while row > 0 {
            row = row - 1;
            let mut min1 = dp[0];
            let mut min1_idx: usize = 0;
            let mut min2 = i32::MAX;
            let mut k = 1usize;
            while k < n {
                if dp[k] < min1 {
                    min2 = min1;
                    min1 = dp[k];
                    min1_idx = k;
                } else if dp[k] < min2 {
                    min2 = dp[k];
                }
                k = k + 1;
            }
            let mut j = 0usize;
            while j < n {
                if j == min1_idx {
                    dp.set(j, grid[row][j] + min2);
                } else {
                    dp.set(j, grid[row][j] + min1);
                }
                j = j + 1;
            }
        }
        let mut result = dp[0];
        let mut k = 1usize;
        while k < n {
            if dp[k] < result {
                result = dp[k];
            }
            k = k + 1;
        }
        result
    }
}

}
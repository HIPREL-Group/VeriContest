use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn row_has_sum_ge2(grid: Seq<i32>, i: int) -> bool
    recommends
        0 <= i,
        3 * i + 3 <= grid.len(),
{
    (grid[3 * i] as int + grid[3 * i + 1] as int + grid[3 * i + 2] as int) >= 2
}

pub open spec fn count_teams_to(grid: Seq<i32>, end: int) -> nat
    recommends
        0 <= end,
        3 * end <= grid.len(),
    decreases end,
{
    if end <= 0 {
        0nat
    } else {
        count_teams_to(grid, end - 1)
            + if row_has_sum_ge2(grid, end - 1) {
                1nat
            } else {
                0nat
            }
    }
}

pub open spec fn count_teams(grid: Seq<i32>, n: int) -> nat
    recommends
        0 <= n,
        3 * n <= grid.len(),
{
    count_teams_to(grid, n)
}

impl Solution {
    pub fn count_teams_implement(grid: Vec<i32>, n: usize) -> (result: usize)
        requires
            1 <= n <= 1000,
            grid.len() == 3 * n,
            forall|i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i] == 0 || grid[i] == 1),
        ensures
            result as int == count_teams(grid@, n as int),
    {
    }
}

}

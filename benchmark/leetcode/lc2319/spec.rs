use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_x_cell(i: int, j: int, n: int) -> bool {
        i == j || i + j == n - 1
    }

    pub open spec fn is_x_matrix(g: Seq<Vec<i32>>) -> bool {
        let n = g.len() as int;
        forall |i: int, j: int|
            0 <= i < n && 0 <= j < n ==>
                if Self::is_x_cell(i, j, n) {
                    #[trigger] g[i][j] != 0
                } else {
                    #[trigger] g[i][j] == 0
                }
    }

    pub fn check_x_matrix(grid: Vec<Vec<i32>>) -> (result: bool)
        requires
            1 <= grid.len() <= 100,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==>
                0 <= #[trigger] grid[i][j] <= 100000,
        ensures
            result == Self::is_x_matrix(grid@),
    {
    }
}

}

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
        let n = grid.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == grid.len(),
                1 <= n <= 100,
                0 <= i <= n,
                forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
                forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid.len() ==>
                    0 <= #[trigger] grid[r][c] <= 100000,
                forall |r: int, c: int| 0 <= r < i as int && 0 <= c < n as int ==>
                    if Self::is_x_cell(r, c, n as int) {
                        grid@[r][c] != 0
                    } else {
                        grid@[r][c] == 0
                    },
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    n == grid.len(),
                    1 <= n <= 100,
                    0 <= i < n,
                    0 <= j <= n,
                    grid[i as int].len() == n,
                    forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
                    forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid.len() ==>
                        0 <= #[trigger] grid[r][c] <= 100000,
                    forall |r: int, c: int| 0 <= r < i as int && 0 <= c < n as int ==>
                        if Self::is_x_cell(r, c, n as int) {
                            grid@[r][c] != 0
                        } else {
                            grid@[r][c] == 0
                        },
                    forall |c: int| 0 <= c < j as int ==>
                        if Self::is_x_cell(i as int, c, n as int) {
                            grid@[i as int][c] != 0
                        } else {
                            grid@[i as int][c] == 0
                        },
                decreases n - j,
            {
                assert(grid[i as int].len() == n);
                if i == j || i + j == n - 1 {
                    if grid[i][j] == 0 {
                        proof {
                            assert(Self::is_x_cell(i as int, j as int, n as int));
                            assert(grid@[i as int][j as int] == 0);
                            assert(!Self::is_x_matrix(grid@));
                        }
                        return false;
                    }
                } else {
                    if grid[i][j] != 0 {
                        proof {
                            assert(!Self::is_x_cell(i as int, j as int, n as int));
                            assert(grid@[i as int][j as int] != 0);
                            assert(!Self::is_x_matrix(grid@));
                        }
                        return false;
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        proof {
            assert forall |r: int, c: int| 0 <= r < n as int && 0 <= c < n as int implies
                if Self::is_x_cell(r, c, n as int) {
                    #[trigger] grid@[r][c] != 0
                } else {
                    #[trigger] grid@[r][c] == 0
                } by {
                assert(0 <= r < i as int);
            }
            assert(Self::is_x_matrix(grid@));
        }
        true
    }
}

}

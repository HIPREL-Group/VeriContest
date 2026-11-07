use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_square(r: int, c: int, x: int, y: int, k: int) -> bool {
        x <= r && r < x + k && y <= c && c < y + k
    }

    pub open spec fn flipped_row(r: int, x: int, k: int) -> int {
        x + k - 1 - (r - x)
    }

    pub fn reverse_submatrix(grid: Vec<Vec<i32>>, x: i32, y: i32, k: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= grid.len() <= 50,
            1 <= grid[0].len() <= 50,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100,
            0 <= (x as int),
            (x as int) < grid.len(),
            0 <= (y as int),
            (y as int) < grid[0].len(),
            1 <= (k as int),
            (k as int) <= grid.len() - (x as int),
            (k as int) <= grid[0].len() - (y as int),
        ensures
            res.len() == grid.len(),
            forall |r: int| 0 <= r < res.len() ==> #[trigger] res[r].len() == grid[r].len(),
            forall |r: int, c: int|
                0 <= r < res.len() && 0 <= c < res[r].len() ==> #[trigger] res[r][c] == if Self::in_square(r, c, (x as int), (y as int), (k as int)) {
                    grid[Self::flipped_row(r, (x as int), (k as int))][c]
                } else {
                    grid[r][c]
                },
    {
    }
}

}

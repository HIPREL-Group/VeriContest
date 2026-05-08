use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn bounding_box(grid: &Vec<Vec<u8>>, n: usize, m: usize) -> (result: (usize, usize, usize, usize))
        requires
            1 <= n <= 50,
            1 <= m <= 50,
            grid.len() == n,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == m,
            forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len()
                ==> #[trigger] grid[i][j] == 0u8 || grid[i][j] == 1u8,
            exists|i: int, j: int| 0 <= i < n && 0 <= j < m && #[trigger] grid[i][j] == 1u8,
        ensures
            result.0 < n,
            result.1 < n,
            result.2 < m,
            result.3 < m,
            result.0 <= result.1,
            result.2 <= result.3,
            forall|i: int, j: int| 0 <= i < n && 0 <= j < m && #[trigger] grid@[i][j] == 1u8
                ==> result.0 as int <= i && i <= result.1 as int
                    && result.2 as int <= j && j <= result.3 as int,
    {
    }
}

}

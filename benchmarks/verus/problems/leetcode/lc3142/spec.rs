use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn satisfies_conditions(grid: Vec<Vec<i32>>) -> (result: bool)
        requires
            1 <= grid.len() <= 10,
            forall |i: int| 0 <= i < grid.len() ==> 1 <= #[trigger] grid[i].len() <= 10,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 9,
        ensures
            result == (
                (forall |i: int, j: int|
                    0 <= i && i + 1 < grid.len() && 0 <= j < grid[0].len() ==>
                    #[trigger] grid[i][j] == grid[i + 1][j])
                &&
                (forall |i: int, j: int|
                    0 <= i < grid.len() && 0 <= j && j + 1 < grid[0].len() ==>
                    #[trigger] grid[i][j] != grid[i][j + 1])
            ),
    {
    }
}

}

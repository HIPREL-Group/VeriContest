use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_symmetric(grid: Vec<u8>) -> (res: bool)
        requires
            grid.len() == 9,
            forall|i: int| 0 <= i < 9 ==> (#[trigger] grid[i] == 0u8 || grid[i] == 1u8),
        ensures
            res == (grid[0] == grid[8] && grid[1] == grid[7] && grid[2] == grid[6] && grid[3] == grid[5]),
    {
    }
}

}

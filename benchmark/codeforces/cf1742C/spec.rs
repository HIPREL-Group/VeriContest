use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn row_all_red(grid: Seq<u8>, r: int) -> bool {
    forall|c: int| 0 <= c < 8 ==> #[trigger] grid[r * 8 + c] == 0u8
}

pub open spec fn any_row_all_red(grid: Seq<u8>) -> bool {
    exists|r: int| 0 <= r < 8 && #[trigger] row_all_red(grid, r)
}

impl Solution {
    pub fn red_last(grid: Vec<u8>) -> (result: bool)
        requires
            grid.len() == 64,
            forall|i: int| 0 <= i < 64 ==> #[trigger] grid[i] <= 2,
        ensures
            result == any_row_all_red(grid@),
    {
    }
}

}

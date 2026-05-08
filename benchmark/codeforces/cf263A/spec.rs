use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn manhattan_to_center(r: int, c: int) -> int
    recommends
        0 <= r < 5,
        0 <= c < 5,
{
    (if r >= 2 { r - 2 } else { 2 - r }) + (if c >= 2 { c - 2 } else { 2 - c })
}

pub open spec fn grid_has_one_at(grid: Seq<i32>, r: int, c: int) -> bool
    recommends
        grid.len() == 25,
        0 <= r < 5,
        0 <= c < 5,
{
    grid[5 * r + c] == 1
}

pub open spec fn is_unique_one_position(grid: Seq<i32>, r: int, c: int) -> bool
    recommends
        grid.len() == 25,
{
    0 <= r < 5 && 0 <= c < 5
    && grid_has_one_at(grid, r, c)
    && (forall|r2: int, c2: int|
        0 <= r2 < 5 && 0 <= c2 < 5 && #[trigger] grid_has_one_at(grid, r2, c2) ==> r2 == r && c2 == c)
}

impl Solution {
    pub fn min_moves_beautiful_matrix(grid: Vec<i32>) -> (res: i32)
        requires
            grid.len() == 25,
            forall|i: int| 0 <= i < 25 ==> (#[trigger] grid[i] == 0 || grid[i] == 1),
            exists|r: int, c: int| is_unique_one_position(grid@, r, c),
        ensures
            forall|r: int, c: int|
                is_unique_one_position(grid@, r, c) ==> (res as int) == manhattan_to_center(r, c),
    {
    }
}

}

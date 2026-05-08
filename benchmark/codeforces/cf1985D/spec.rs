use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_mark(grid: Seq<Vec<i32>>, i: int, j: int) -> bool
    recommends
        0 <= i < grid.len(),
        0 <= j < grid[0].len(),
{
    grid[i][j] == 1
}

pub open spec fn is_min_marked_row(grid: Seq<Vec<i32>>, r: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= r < grid.len()
    && exists|j: int| 0 <= j < grid[0].len() && #[trigger] is_mark(grid, r, j)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> r <= i
}

pub open spec fn is_max_marked_row(grid: Seq<Vec<i32>>, r: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= r < grid.len()
    && exists|j: int| 0 <= j < grid[0].len() && #[trigger] is_mark(grid, r, j)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> i <= r
}

pub open spec fn is_min_marked_col(grid: Seq<Vec<i32>>, c: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= c < grid[0].len()
    && exists|i: int| 0 <= i < grid.len() && #[trigger] is_mark(grid, i, c)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> c <= j
}

pub open spec fn is_max_marked_col(grid: Seq<Vec<i32>>, c: int) -> bool
    recommends
        0 < grid.len(),
        0 < grid[0].len(),
{
    0 <= c < grid[0].len()
    && exists|i: int| 0 <= i < grid.len() && #[trigger] is_mark(grid, i, c)
    && forall|i: int, j: int|
        0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid, i, j) ==> j <= c
}

impl Solution {
    pub fn manhattan_circle_center(grid: Vec<Vec<i32>>) -> (center: (i32, i32))
        requires
            0 < grid.len(),
            0 < grid[0].len(),
            grid.len() <= 200000,
            grid[0].len() <= 200000,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall|i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[0].len() ==> (#[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1),
            exists|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid@, i, j),
        ensures
            1 <= center.0 <= grid.len() as i32,
            1 <= center.1 <= grid[0].len() as i32,
            exists|rmin: int, rmax: int, cmin: int, cmax: int|
                is_min_marked_row(grid@, rmin)
                && is_max_marked_row(grid@, rmax)
                && is_min_marked_col(grid@, cmin)
                && is_max_marked_col(grid@, cmax)
                && center.0 as int == (rmin + rmax) / 2 + 1
                && center.1 as int == (cmin + cmax) / 2 + 1,
    {
    }
}

}

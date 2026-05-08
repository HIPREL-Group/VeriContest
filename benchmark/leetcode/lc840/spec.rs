use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cols(grid: Seq<Vec<i32>>) -> int {
        if grid.len() > 0 { grid[0].len() as int } else { 0 }
    }

    pub open spec fn candidate_rows(grid: Seq<Vec<i32>>) -> int {
        if grid.len() >= 3 { grid.len() - 2 } else { 0 }
    }

    pub open spec fn candidate_cols(grid: Seq<Vec<i32>>) -> int {
        if Self::cols(grid) >= 3 { Self::cols(grid) - 2 } else { 0 }
    }

    pub open spec fn is_magic_square_at(grid: Seq<Vec<i32>>, r: int, c: int) -> bool
        recommends
            0 <= r < grid.len(),
            0 <= c < Self::cols(grid),
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == Self::cols(grid),
    {
        let a = grid[r][c] as int;
        let b = grid[r][c + 1] as int;
        let c1 = grid[r][c + 2] as int;
        let d = grid[r + 1][c] as int;
        let e = grid[r + 1][c + 1] as int;
        let f = grid[r + 1][c + 2] as int;
        let g = grid[r + 2][c] as int;
        let h = grid[r + 2][c + 1] as int;
        let i = grid[r + 2][c + 2] as int;

        r + 2 < grid.len()
            && c + 2 < Self::cols(grid)
            && 1 <= a <= 9
            && 1 <= b <= 9
            && 1 <= c1 <= 9
            && 1 <= d <= 9
            && 1 <= e <= 9
            && 1 <= f <= 9
            && 1 <= g <= 9
            && 1 <= h <= 9
            && 1 <= i <= 9
            && a != b
            && a != c1
            && a != d
            && a != e
            && a != f
            && a != g
            && a != h
            && a != i
            && b != c1
            && b != d
            && b != e
            && b != f
            && b != g
            && b != h
            && b != i
            && c1 != d
            && c1 != e
            && c1 != f
            && c1 != g
            && c1 != h
            && c1 != i
            && d != e
            && d != f
            && d != g
            && d != h
            && d != i
            && e != f
            && e != g
            && e != h
            && e != i
            && f != g
            && f != h
            && f != i
            && g != h
            && g != i
            && h != i
            && a + b + c1 == 15
            && d + e + f == 15
            && g + h + i == 15
            && a + d + g == 15
            && b + e + h == 15
            && c1 + f + i == 15
            && a + e + i == 15
            && c1 + e + g == 15
    }

    pub open spec fn row_magic_count_prefix(grid: Seq<Vec<i32>>, r: int, j_end: int) -> int
        recommends
            0 <= r < Self::candidate_rows(grid),
            0 <= j_end <= Self::candidate_cols(grid),
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == Self::cols(grid),
        decreases j_end,
    {
        if j_end <= 0 {
            0
        } else {
            Self::row_magic_count_prefix(grid, r, j_end - 1)
                + if Self::is_magic_square_at(grid, r, j_end - 1) { 1int } else { 0int }
        }
    }

    pub open spec fn total_magic_count_prefix(grid: Seq<Vec<i32>>, i_end: int) -> int
        recommends
            0 <= i_end <= Self::candidate_rows(grid),
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == Self::cols(grid),
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            Self::total_magic_count_prefix(grid, i_end - 1)
                + Self::row_magic_count_prefix(grid, i_end - 1, Self::candidate_cols(grid))
        }
    }

    pub fn num_magic_squares_inside(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 10,
            1 <= grid[0].len() <= 10,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall|i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 15,
        ensures
            result as int == Self::total_magic_count_prefix(grid@, Self::candidate_rows(grid@)),
    {
    }
}

}

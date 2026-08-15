use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn adjacent(r1: int, c1: int, r2: int, c2: int) -> bool {
        (r1 == r2 && (c1 + 1 == c2 || c2 + 1 == c1))
            || (c1 == c2 && (r1 + 1 == r2 || r2 + 1 == r1))
    }

    pub open spec fn is_land(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        0 <= r < rows && 0 <= c < cols && grid[r][c] == 1
    }

    pub open spec fn reachable(grid: Seq<Vec<i32>>, rows: int, cols: int, r1: int, c1: int, r2: int, c2: int, fuel: nat) -> bool
        decreases fuel
    {
        if r1 == r2 && c1 == c2 {
            Self::is_land(grid, rows, cols, r1, c1)
        } else if fuel == 0 {
            false
        } else {
            Self::is_land(grid, rows, cols, r1, c1)
            && exists|r3: int, c3: int|
                Self::adjacent(r1, c1, r3, c3)
                && Self::is_land(grid, rows, cols, r3, c3)
                && Self::reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat)
        }
    }

    pub open spec fn exactly_one_island(grid: Seq<Vec<i32>>, rows: int, cols: int) -> bool {
        (exists|r: int, c: int| Self::is_land(grid, rows, cols, r, c))
        && (forall|r1: int, c1: int, r2: int, c2: int|
            Self::is_land(grid, rows, cols, r1, c1) && Self::is_land(grid, rows, cols, r2, c2)
            ==> Self::reachable(grid, rows, cols, r1, c1, r2, c2, (rows * cols) as nat))
    }

    pub open spec fn is_water(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        0 <= r < rows && 0 <= c < cols && grid[r][c] == 0
    }

    pub open spec fn water_reachable(grid: Seq<Vec<i32>>, rows: int, cols: int, r1: int, c1: int, r2: int, c2: int, fuel: nat) -> bool
        decreases fuel
    {
        if r1 == r2 && c1 == c2 {
            Self::is_water(grid, rows, cols, r1, c1)
        } else if fuel == 0 {
            false
        } else {
            Self::is_water(grid, rows, cols, r1, c1)
            && exists|r3: int, c3: int|
                Self::adjacent(r1, c1, r3, c3)
                && Self::is_water(grid, rows, cols, r3, c3)
                && Self::water_reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat)
        }
    }

    pub open spec fn is_border_water(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        Self::is_water(grid, rows, cols, r, c) && (r == 0 || r == rows - 1 || c == 0 || c == cols - 1)
    }

    pub open spec fn no_lakes(grid: Seq<Vec<i32>>, rows: int, cols: int) -> bool {
        forall|r: int, c: int| Self::is_water(grid, rows, cols, r, c) ==>
            exists|br: int, bc: int| Self::is_border_water(grid, rows, cols, br, bc)
                && Self::water_reachable(grid, rows, cols, r, c, br, bc, (rows * cols) as nat)
    }

    pub open spec fn cell_contribution(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> int {
        if grid[r][c] == 1 {
            let top = if r > 0 && grid[r - 1][c] == 1 { 2int } else { 0int };
            let left = if c > 0 && grid[r][c - 1] == 1 { 2int } else { 0int };
            4 - top - left
        } else {
            0
        }
    }

    pub open spec fn row_perimeter(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c_end: int) -> int
        decreases c_end
    {
        if c_end <= 0 {
            0
        } else {
            Self::row_perimeter(grid, rows, cols, r, c_end - 1)
                + Self::cell_contribution(grid, rows, cols, r, c_end - 1)
        }
    }

    pub open spec fn island_perimeter_spec(grid: Seq<Vec<i32>>, rows: int, cols: int, r_end: int) -> int
        decreases r_end
    {
        if r_end <= 0 {
            0
        } else {
            Self::island_perimeter_spec(grid, rows, cols, r_end - 1)
                + Self::row_perimeter(grid, rows, cols, r_end - 1, cols)
        }
    }

    pub fn island_perimeter(grid: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= grid.len() <= 100,
            1 <= grid[0].len() <= 100,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len() ==> #[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1,
            Self::exactly_one_island(grid@, grid.len() as int, grid[0].len() as int),
            Self::no_lakes(grid@, grid.len() as int, grid[0].len() as int),
        ensures
            res as int == Self::island_perimeter_spec(grid@, grid.len() as int, grid[0].len() as int, grid.len() as int),
    {
    }
}

}

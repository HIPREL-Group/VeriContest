use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    
    
    pub open spec fn cherry_value(grid: Seq<Vec<i32>>, row: int, c1: int, c2: int) -> int {
        if c1 == c2 {
            grid[row][c1] as int
        } else {
            grid[row][c1] as int + grid[row][c2] as int
        }
    }

    
    
    
    
    
    
    
    pub open spec fn dp_val(grid: Seq<Vec<i32>>, row: int, c1: int, c2: int) -> int
        decreases grid.len() - row
    {
        let n = grid[0].len() as int;
        if row < 0 || row >= grid.len() || c1 < 0 || c1 >= n || c2 < 0 || c2 >= n {
            0
        } else if row >= grid.len() - 1 {
            Self::cherry_value(grid, row, c1, c2)
        } else {
            Self::cherry_value(grid, row, c1, c2) + Self::max2(
                Self::max2(
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 - 1, c2 - 1),
                        Self::dp_val(grid, row + 1, c1 - 1, c2)
                    ),
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 - 1, c2 + 1),
                        Self::dp_val(grid, row + 1, c1, c2 - 1)
                    )
                ),
                Self::max2(
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1, c2),
                        Self::dp_val(grid, row + 1, c1, c2 + 1)
                    ),
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 + 1, c2 - 1),
                        Self::max2(
                            Self::dp_val(grid, row + 1, c1 + 1, c2),
                            Self::dp_val(grid, row + 1, c1 + 1, c2 + 1)
                        )
                    )
                )
            )
        }
    }

    pub fn cherry_pickup(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= grid.len() <= 70,
            2 <= grid[0].len() <= 70,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 0 <= #[trigger] grid[i][j] <= 100,
        ensures
            result as int == Self::dp_val(grid@, 0, 0, grid[0].len() as int - 1),
    {
    }
}

}

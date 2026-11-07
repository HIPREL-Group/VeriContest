use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;














impl Solution {
    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn max4(a: int, b: int, c: int, d: int) -> int {
        Self::max2(Self::max2(a, b), Self::max2(c, d))
    }

    pub open spec fn min4(a: int, b: int, c: int, d: int) -> int {
        Self::min2(Self::min2(a, b), Self::min2(c, d))
    }

    
    
    pub open spec fn max_prod(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        recommends
            0 <= i < grid.len(),
            0 <= j < grid[i].len(),
        decreases i + j when i >= 0 && j >= 0
    {
        if i + j <= 0 {
            grid[0][0] as int
        } else if i <= 0 {
            Self::max_prod(grid, 0, j - 1) * (grid[0][j] as int)
        } else if j <= 0 {
            Self::max_prod(grid, i - 1, 0) * (grid[i][0] as int)
        } else {
            let v = grid[i][j] as int;
            Self::max4(
                Self::max_prod(grid, i - 1, j) * v,
                Self::min_prod(grid, i - 1, j) * v,
                Self::max_prod(grid, i, j - 1) * v,
                Self::min_prod(grid, i, j - 1) * v,
            )
        }
    }

    
    
    pub open spec fn min_prod(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        recommends
            0 <= i < grid.len(),
            0 <= j < grid[i].len(),
        decreases i + j when i >= 0 && j >= 0
    {
        if i + j <= 0 {
            grid[0][0] as int
        } else if i <= 0 {
            Self::min_prod(grid, 0, j - 1) * (grid[0][j] as int)
        } else if j <= 0 {
            Self::min_prod(grid, i - 1, 0) * (grid[i][0] as int)
        } else {
            let v = grid[i][j] as int;
            Self::min4(
                Self::max_prod(grid, i - 1, j) * v,
                Self::min_prod(grid, i - 1, j) * v,
                Self::max_prod(grid, i, j - 1) * v,
                Self::min_prod(grid, i, j - 1) * v,
            )
        }
    }

    pub fn max_product_path(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 15,
            1 <= grid[0].len() <= 15,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len()
                    ==> -4 <= #[trigger] grid[i][j] <= 4,
        ensures
            Self::max_prod(grid@, grid@.len() as int - 1, grid[0].len() as int - 1) < 0
                ==> result == -1i32,
            Self::max_prod(grid@, grid@.len() as int - 1, grid[0].len() as int - 1) >= 0
                ==> result == (Self::max_prod(grid@, grid@.len() as int - 1, grid[0].len() as int - 1) % 1_000_000_007) as i32,
    {
    }
}

}

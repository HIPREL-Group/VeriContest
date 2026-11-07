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

    fn max2_i64(a: i64, b: i64) -> (res: i64)
        ensures
            res as int == Self::max2(a as int, b as int),
    {
        if a >= b { a } else { b }
    }

    fn min2_i64(a: i64, b: i64) -> (res: i64)
        ensures
            res as int == Self::min2(a as int, b as int),
    {
        if a <= b { a } else { b }
    }

    fn max4_i64(a: i64, b: i64, c: i64, d: i64) -> (res: i64)
        ensures
            res as int == Self::max4(a as int, b as int, c as int, d as int),
    {
        Self::max2_i64(Self::max2_i64(a, b), Self::max2_i64(c, d))
    }

    fn min4_i64(a: i64, b: i64, c: i64, d: i64) -> (res: i64)
        ensures
            res as int == Self::min4(a as int, b as int, c as int, d as int),
    {
        Self::min2_i64(Self::min2_i64(a, b), Self::min2_i64(c, d))
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
        let m = grid.len();
        let n = grid[0].len();

        let mut dp_max: Vec<i64> = Vec::new();
        let mut dp_min: Vec<i64> = Vec::new();

        dp_max.push(grid[0][0] as i64);
        dp_min.push(grid[0][0] as i64);

        let mut j = 1usize;
        while j < n {
            let val = grid[0][j] as i64;
            dp_max.push(dp_max[j - 1] * val);
            dp_min.push(dp_min[j - 1] * val);
            j += 1;
        }

        let mut i = 1usize;
        while i < m {
            let v0 = grid[i][0] as i64;
            let old_mx = dp_max[0];
            let old_mn = dp_min[0];
            dp_max.set(0, old_mx * v0);
            dp_min.set(0, old_mn * v0);

            let mut j = 1usize;
            while j < n {
                let above_mx = dp_max[j];
                let above_mn = dp_min[j];
                let left_mx = dp_max[j - 1];
                let left_mn = dp_min[j - 1];
                let v = grid[i][j] as i64;
                let a = above_mx * v;
                let b = above_mn * v;
                let c = left_mx * v;
                let d = left_mn * v;
                let new_mx = Self::max4_i64(a, b, c, d);
                let new_mn = Self::min4_i64(a, b, c, d);
                dp_max.set(j, new_mx);
                dp_min.set(j, new_mn);
                j += 1;
            }

            i += 1;
        }

        if dp_max[n - 1] < 0 {
            -1i32
        } else {
            (dp_max[n - 1] % 1_000_000_007i64) as i32
        }
    }
}

}

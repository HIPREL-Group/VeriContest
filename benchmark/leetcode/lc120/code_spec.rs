use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn path_sum(triangle: Seq<Vec<i32>>, row: int, col: int) -> int
        recommends
            0 <= row < triangle.len(),
            0 <= col < triangle[row].len(),
        decreases triangle.len() - row
    {
        triangle[row][col] as int + if row + 1 >= triangle.len() {
            0
        } else {
            Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1))
        }
    }

    fn min_i32(a: i32, b: i32) -> (res: i32)
        ensures
            res as int == Self::min2(a as int, b as int),
    {
        if a <= b { a } else { b }
    }

    pub fn minimum_total(triangle: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= triangle.len() <= 200,
            triangle[0].len() == 1,
            forall |row: int| 0 <= row < triangle.len() ==> #[trigger] triangle[row].len() == row + 1,
            forall |row: int, col: int|
                0 <= row < triangle.len() && 0 <= col < triangle[row].len() ==> -10000 <= #[trigger] triangle[row][col] <= 10000,
        ensures
            res as int == Self::path_sum(triangle@, 0, 0),
    {
        let rows = triangle.len();
        let mut dp = triangle[rows - 1].clone();
        let mut row = rows - 1;
        while row > 0 {
            row = row - 1;
            let mut col = 0usize;
            while col <= row {
                let best_child = Self::min_i32(dp[col], dp[col + 1]);
                let value = triangle[row][col] + best_child;
                dp.set(col, value);
                col = col + 1;
            }
        }
        dp[0]
    }
}

}

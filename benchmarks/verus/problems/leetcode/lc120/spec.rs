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
    }
}

}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_boomerang(points: Vec<Vec<i32>>) -> (res: bool)
        requires
            points.len() == 3,
            points[0].len() == 2,
            points[1].len() == 2,
            points[2].len() == 2,
            0 <= points[0][0] <= 100,
            0 <= points[0][1] <= 100,
            0 <= points[1][0] <= 100,
            0 <= points[1][1] <= 100,
            0 <= points[2][0] <= 100,
            0 <= points[2][1] <= 100,
        ensures
            res == ((points[1][0] as int - points[0][0] as int) * (points[2][1] as int - points[0][1] as int)
                != (points[2][0] as int - points[0][0] as int) * (points[1][1] as int - points[0][1] as int)),
    {
    }
}

}

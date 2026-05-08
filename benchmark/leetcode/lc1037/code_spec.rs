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
        let x0 = points[0][0];
        let y0 = points[0][1];
        let x1 = points[1][0];
        let y1 = points[1][1];
        let x2 = points[2][0];
        let y2 = points[2][1];
        (x1 - x0) * (y2 - y0) != (x2 - x0) * (y1 - y0)
    }
}

}

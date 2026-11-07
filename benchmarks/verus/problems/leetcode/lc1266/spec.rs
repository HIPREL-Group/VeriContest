use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn chebyshev(dx: int, dy: int) -> int {
        if dx >= dy { dx } else { dy }
    }

    pub open spec fn total_time(points: Seq<Vec<i32>>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::total_time(points, n - 1) + Self::chebyshev(
                Self::abs_diff(points[n]@[0] as int, points[n - 1]@[0] as int),
                Self::abs_diff(points[n]@[1] as int, points[n - 1]@[1] as int),
            )
        }
    }

    pub fn min_time_to_visit_all_points(points: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= points.len() <= 100,
            forall |i: int| 0 <= i < points.len() ==>
                (#[trigger] points[i]).len() == 2
                && -1000 <= points[i][0] <= 1000
                && -1000 <= points[i][1] <= 1000,
        ensures
            res as int == Self::total_time(points@, points@.len() as int - 1),
    {
    }
}

}

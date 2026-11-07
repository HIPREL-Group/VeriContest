use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs(val: int) -> int {
    if val < 0 { -val } else { val }
}

pub open spec fn dist(x: int, y: int, x1: int, y1: int) -> int {
    abs(x - x1) + abs(y - y1)
}

pub open spec fn valid_pt(p: Seq<i32>) -> bool {
    p.len() == 2 && 1 <= p[0] && p[0] <= 10000 && 1 <= p[1] && p[1] <= 10000
}

impl Solution {
    pub fn nearest_valid_point(x: i32, y: i32, points: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= points.len() <= 10000,
            forall |i: int| #![trigger valid_pt(points[i]@)] 0 <= i < points.len() ==> valid_pt(points[i]@),
            1 <= x <= 10000,
            1 <= y <= 10000,
        ensures
            result >= -1,
            result < points.len(),
            result == -1 ==> forall |i: int| 0 <= i < points.len() && valid_pt(points[i]@) ==> (#[trigger] points[i][0] != x && #[trigger] points[i][1] != y),
            result != -1 ==> (
                valid_pt(points[result as int]@) && (#[trigger] points[result as int][0] == x || #[trigger] points[result as int][1] == y)
            ) &&
            forall |i: int| 0 <= i < points.len() && valid_pt(points[i]@) && (#[trigger] points[i][0] == x || #[trigger] points[i][1] == y) ==>
                dist(x as int, y as int, #[trigger] points[i][0] as int, #[trigger] points[i][1] as int) > dist(x as int, y as int, points[result as int][0] as int, points[result as int][1] as int) ||
                (dist(x as int, y as int, points[i][0] as int, points[i][1] as int) == dist(x as int, y as int, points[result as int][0] as int, points[result as int][1] as int) && result <= i),
    {
    }
}

}

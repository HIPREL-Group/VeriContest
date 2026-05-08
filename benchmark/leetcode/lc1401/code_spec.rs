use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn clamp(val: int, lo: int, hi: int) -> int {
    if val < lo {
        lo
    } else if val > hi {
        hi
    } else {
        val
    }
}

pub open spec fn overlaps(radius: int, x_center: int, y_center: int, x1: int, y1: int, x2: int, y2: int) -> bool {
    let nearest_x = clamp(x_center, x1, x2);
    let nearest_y = clamp(y_center, y1, y2);
    let dx = x_center - nearest_x;
    let dy = y_center - nearest_y;
    dx * dx + dy * dy <= radius * radius
}

impl Solution {
    pub fn check_overlap(radius: i32, x_center: i32, y_center: i32, x1: i32, y1: i32, x2: i32, y2: i32) -> (res: bool)
        requires
            1 <= radius <= 2000,
            -10_000 <= x_center <= 10_000,
            -10_000 <= y_center <= 10_000,
            -10_000 <= x1 <= 10_000,
            -10_000 <= y1 <= 10_000,
            -10_000 <= x2 <= 10_000,
            -10_000 <= y2 <= 10_000,
            x1 < x2,
            y1 < y2,
        ensures
            res == overlaps(radius as int, x_center as int, y_center as int, x1 as int, y1 as int, x2 as int, y2 as int),
    {
        let nearest_x = if x_center < x1 { x1 } else if x_center > x2 { x2 } else { x_center };
        let nearest_y = if y_center < y1 { y1 } else if y_center > y2 { y2 } else { y_center };
        let dx = x_center - nearest_x;
        let dy = y_center - nearest_y;
        dx * dx + dy * dy <= radius * radius
    }
}

}

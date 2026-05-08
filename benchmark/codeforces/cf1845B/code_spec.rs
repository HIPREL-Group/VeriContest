use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs(v: int) -> int {
    if v >= 0 { v } else { -v }
}

pub open spec fn spec_overlap(a: int, b: int, c: int) -> int {
    let db = b - a;
    let dc = c - a;
    if (db > 0 && dc > 0) || (db < 0 && dc < 0) {
        if spec_abs(db) < spec_abs(dc) {
            spec_abs(db)
        } else {
            spec_abs(dc)
        }
    } else {
        0
    }
}

pub open spec fn spec_min_meeting_cells(ax: int, ay: int, bx: int, by: int, cx: int, cy: int) -> int {
    1 + spec_overlap(ax, bx, cx) + spec_overlap(ay, by, cy)
}

impl Solution {
    pub fn min_meeting_cells(ax: i64, ay: i64, bx: i64, by: i64, cx: i64, cy: i64) -> (res: i64)
        requires
            -1000000000 <= ax <= 1000000000,
            -1000000000 <= ay <= 1000000000,
            -1000000000 <= bx <= 1000000000,
            -1000000000 <= by <= 1000000000,
            -1000000000 <= cx <= 1000000000,
            -1000000000 <= cy <= 1000000000,
        ensures
            res as int == spec_min_meeting_cells(ax as int, ay as int, bx as int, by as int, cx as int, cy as int),
    {
        let mut ans: i64 = 1;

        let dx_b = bx - ax;
        let dx_c = cx - ax;
        if (dx_b > 0 && dx_c > 0) || (dx_b < 0 && dx_c < 0) {
            let ab = if dx_b >= 0 { dx_b } else { -dx_b };
            let ac = if dx_c >= 0 { dx_c } else { -dx_c };
            ans += if ab < ac { ab } else { ac };
        }

        let dy_b = by - ay;
        let dy_c = cy - ay;
        if (dy_b > 0 && dy_c > 0) || (dy_b < 0 && dy_c < 0) {
            let ab = if dy_b >= 0 { dy_b } else { -dy_b };
            let ac = if dy_c >= 0 { dy_c } else { -dy_c };
            ans += if ab < ac { ab } else { ac };
        }

        ans
    }
}

}

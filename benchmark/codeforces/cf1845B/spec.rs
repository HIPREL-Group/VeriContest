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
    }
}

}

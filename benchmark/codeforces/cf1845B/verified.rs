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
        let mut x_part: i64 = 0;

        let dx_b = bx - ax;
        let dx_c = cx - ax;
        if (dx_b > 0 && dx_c > 0) || (dx_b < 0 && dx_c < 0) {
            let ab = if dx_b >= 0 { dx_b } else { -dx_b };
            let ac = if dx_c >= 0 { dx_c } else { -dx_c };
            ans += if ab < ac { ab } else { ac };
            x_part = if ab < ac { ab } else { ac };
            proof {
                assert(spec_abs((bx as int) - (ax as int)) == ab as int);
                assert(spec_abs((cx as int) - (ax as int)) == ac as int);
                if ab < ac {
                    assert(x_part as int == spec_abs((bx as int) - (ax as int)));
                } else {
                    assert(x_part as int == spec_abs((cx as int) - (ax as int)));
                }
                assert(x_part as int == spec_overlap(ax as int, bx as int, cx as int));
            }
        } else {
            proof {
                assert(spec_overlap(ax as int, bx as int, cx as int) == 0);
                assert(x_part as int == spec_overlap(ax as int, bx as int, cx as int));
            }
        }

        let mut y_part: i64 = 0;
        let dy_b = by - ay;
        let dy_c = cy - ay;
        if (dy_b > 0 && dy_c > 0) || (dy_b < 0 && dy_c < 0) {
            let ab = if dy_b >= 0 { dy_b } else { -dy_b };
            let ac = if dy_c >= 0 { dy_c } else { -dy_c };
            ans += if ab < ac { ab } else { ac };
            y_part = if ab < ac { ab } else { ac };
            proof {
                assert(spec_abs((by as int) - (ay as int)) == ab as int);
                assert(spec_abs((cy as int) - (ay as int)) == ac as int);
                if ab < ac {
                    assert(y_part as int == spec_abs((by as int) - (ay as int)));
                } else {
                    assert(y_part as int == spec_abs((cy as int) - (ay as int)));
                }
                assert(y_part as int == spec_overlap(ay as int, by as int, cy as int));
            }
        } else {
            proof {
                assert(spec_overlap(ay as int, by as int, cy as int) == 0);
                assert(y_part as int == spec_overlap(ay as int, by as int, cy as int));
            }
        }

        proof {
            assert(ans as int == 1 + x_part as int + y_part as int);
            assert(ans as int == spec_min_meeting_cells(ax as int, ay as int, bx as int, by as int, cx as int, cy as int));
        }

        ans
    }
}

}

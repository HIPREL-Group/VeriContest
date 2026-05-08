use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

pub open spec fn sum_dist(x1: int, x2: int, x3: int, m: int) -> int {
    abs_diff(x1, m) + abs_diff(x2, m) + abs_diff(x3, m)
}

impl Solution {
    pub fn min_total_meeting_distance(x1: i32, x2: i32, x3: i32) -> (res: i32)
        requires
            1 <= x1 as int <= 100,
            1 <= x2 as int <= 100,
            1 <= x3 as int <= 100,
            x1 as int != x2 as int,
            x1 as int != x3 as int,
            x2 as int != x3 as int,
        ensures
            2 <= res as int <= 99,
            forall |m: int| #[trigger] sum_dist(x1 as int, x2 as int, x3 as int, m) >= res as int,
            exists |m: int| #[trigger] sum_dist(x1 as int, x2 as int, x3 as int, m) == res as int,
    {
        let mut coords: Vec<i32> = Vec::new();
        coords.push(x1);
        coords.push(x2);
        coords.push(x3);
        let mut mn = coords[0];
        let mut mx = coords[0];
        let mut i = 1usize;
        while i < 3 {
            if coords[i] < mn {
                mn = coords[i];
            }
            if coords[i] > mx {
                mx = coords[i];
            }
            i = i + 1;
        }
        mx - mn
    }
}

}

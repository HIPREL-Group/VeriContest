use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn square(x: int) -> int {
    x * x
}

pub open spec fn distance_sq(x: int, y: int, x2: int, y2: int) -> int {
    square(x2 - x) + square(y2 - y)
}

pub open spec fn jump_sq(r: int) -> int {
    square(2 * r)
}

pub open spec fn can_reach_in_steps(r: int, x: int, y: int, x2: int, y2: int, steps: int) -> bool {
    0 <= steps && distance_sq(x, y, x2, y2) <= jump_sq(r) * steps * steps
}

impl Solution {
    pub fn min_steps_to_target(r: i128, x: i128, y: i128, x2: i128, y2: i128) -> (res: i128)
        requires
            1 <= r <= 100000,
            -100000 <= x <= 100000,
            -100000 <= y <= 100000,
            -100000 <= x2 <= 100000,
            -100000 <= y2 <= 100000,
        ensures
            0 <= res <= 200000,
            can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, res as int),
            forall|k: int|
                0 <= k < res as int ==> !can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, k),
    {
        let dx = x2 - x;
        let dy = y2 - y;
        let dist_sq = dx * dx + dy * dy;
        let two_r = 2 * r;
        let jump_sq_val = two_r * two_r;
        let mut ans = 0i128;
        while ans < 200000 && jump_sq_val * ans * ans < dist_sq {
            ans += 1;
        }
        ans
    }
}

}

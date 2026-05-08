use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_reachable(n: int, presses: int) -> int
        recommends n >= 0, presses >= 0
    {
        if presses == 0 {
            1
        } else if n == 1 {
            2
        } else if n == 2 {
            if presses == 1 {
                3
            } else {
                4
            }
        } else {
            if presses == 1 {
                4
            } else if presses == 2 {
                7
            } else {
                8
            }
        }
    }

    pub fn flip_lights(n: i32, presses: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            0 <= presses <= 1000,
        ensures
            result >= 0,
            result == Self::count_reachable(n as int, presses as int),
    {
        if presses == 0 {
            return 1;
        }
        if n == 1 {
            return 2;
        }
        if n == 2 {
            if presses == 1 {
                return 3;
            }
            return 4;
        }
        if presses == 1 {
            return 4;
        }
        if presses == 2 {
            return 7;
        }
        return 8;
    }
}

}

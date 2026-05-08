use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn level_cubes(i: int) -> int {
    i * (i + 1) / 2
}

pub open spec fn cumulative_cubes(h: int) -> int
    decreases h,
{
    if h <= 0 {
        0int
    } else {
        cumulative_cubes(h - 1) + level_cubes(h)
    }
}

impl Solution {
    pub fn max_pyramid_height(n: u64) -> (result: u64)
        requires
            1 <= n <= 10000,
        ensures
            cumulative_cubes(result as int) <= n as int,
            cumulative_cubes(result as int + 1) > n as int,
    {
        let mut h: u64 = 0;
        let mut total: u64 = 0;
        let mut done: bool = false;
        while !done {
            if h >= 10001 {
                done = true;
            } else {
                let level = (h + 1) * (h + 2) / 2;
                if total + level > n {
                    done = true;
                } else {
                    total = total + level;
                    h = h + 1;
                }
            }
        }
        h
    }
}

}

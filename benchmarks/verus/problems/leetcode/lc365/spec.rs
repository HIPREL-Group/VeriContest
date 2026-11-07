use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_gcd(a: u32, b: u32) -> u32
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Solution::spec_gcd(b, a % b)
        }
    }

    pub open spec fn can_measure_spec(x: u32, y: u32, target: u32) -> bool {
        target <= x + y && Solution::spec_gcd(x, y) > 0 && target % Solution::spec_gcd(x, y) == 0
    }

    pub fn can_measure_water(x: i32, y: i32, target: i32) -> (res: bool)
        requires
            1 <= x <= 1000,
            1 <= y <= 1000,
            1 <= target <= 1000,
        ensures
            res == Solution::can_measure_spec(x as u32, y as u32, target as u32),
    {
    }
}

}

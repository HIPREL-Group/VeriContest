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
        let x_u: u32 = x as u32;
        let y_u: u32 = y as u32;
        let target_u: u32 = target as u32;
        if target_u > x_u + y_u {
            return false;
        }
        let mut a: u32 = x_u;
        let mut b: u32 = y_u;
        while b != 0 {
            let rem: u32 = a % b;
            a = b;
            b = rem;
        }
        target_u % a == 0
    }
}

}

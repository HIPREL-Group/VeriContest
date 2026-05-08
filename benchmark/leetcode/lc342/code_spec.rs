use vstd::arithmetic::{logarithm::log, power::pow};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_power_of_four(n: int) -> bool {
        if n <= 0 {
            false
        } else {
            pow(4, log(4, n) as nat) == n
        }
    }

    pub fn is_power_of_four(n: i32) -> (res: bool)
        requires
            -2_147_483_648 <= n <= 2_147_483_647,
        ensures
            res == Self::spec_is_power_of_four(n as int),
    {
        if n <= 0 {
            false
        } else {
            let mut x = n;
            while x > 1 && x % 4 == 0 {
                x = x / 4;
            }
            x == 1
        }
    }
}

} 

use vstd::arithmetic::{logarithm::log, power::pow};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_power_of_three(n: int) -> bool {
        if n <= 0 {
            false
        } else {
            pow(3, log(3, n) as nat) == n
        }
    }

    pub fn is_power_of_three(n: i32) -> (res: bool)
        requires
            -2_147_483_648 <= n <= 2_147_483_647,
        ensures
            res == Self::spec_is_power_of_three(n as int),
    {
    }
}

} 

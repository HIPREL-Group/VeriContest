use vstd::arithmetic::{logarithm::log, power2::pow2};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_power_of_two(n: int) -> bool {
        if n <= 0 {
            false
        } else {
            pow2(log(2, n) as nat) == n
        }
    }

    pub fn is_power_of_two(n: i32) -> (result: bool)
        requires
            -2_147_483_648 <= n <= 2_147_483_647,
        ensures
            result == Self::spec_is_power_of_two(n as int),
    {
    }
}

} 

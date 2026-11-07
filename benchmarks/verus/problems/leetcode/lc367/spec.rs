use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_perfect_square(num: int) -> bool {
        exists|k: nat| pow(k as int, 2) == num
    }

    pub fn is_perfect_square(num: i32) -> bool
        requires
            1 <= num <= i32::MAX,
        returns
            Self::spec_is_perfect_square(num as int),
    {
    }
}

} 

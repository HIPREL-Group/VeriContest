use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_steps(n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else if n % 2 == 0 {
            1 + Self::spec_steps(n / 2)
        } else {
            1 + Self::spec_steps(n - 1)
        }
    }

    pub fn number_of_steps(num: i32) -> (result: i32)
        requires
            0 <= num <= 1_000_000,
        ensures
            result == Self::spec_steps(num as int),
    {
    }
}

}

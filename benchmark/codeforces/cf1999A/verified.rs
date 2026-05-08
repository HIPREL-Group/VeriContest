use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_two_digit_digit_sum(n: int) -> int {
        n / 10 + n % 10
    }

    pub fn two_digit_digit_sum(n: i32) -> (sum: i32)
        requires
            10 <= n <= 99,
        ensures
            sum as int == Self::spec_two_digit_digit_sum(n as int),
    {
        let tens = n / 10;
        let ones = n % 10;
        proof {
            assert((n as int) / 10 == tens as int);
            assert((n as int) % 10 == ones as int);
        }
        tens + ones
    }
}

}

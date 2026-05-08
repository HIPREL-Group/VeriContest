use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const M: u64 = 1_000_000_007;

    pub open spec fn count_good_numbers_spec_inner(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            1
        } else if n % 2 == 1 {
            5 * Self::count_good_numbers_spec_inner((n - 1) as nat)
        } else {
            4 * Self::count_good_numbers_spec_inner((n - 1) as nat)
        }
    }

    pub open spec fn count_good_numbers_spec(n: nat) -> nat {
        Self::count_good_numbers_spec_inner(n) % Self::M as nat
    }

    pub fn count_good_numbers(n: i64) -> (res: i32)
        requires
            1 <= n <= pow(10, 15),
        ensures
            res == Self::count_good_numbers_spec(n as nat) as i32,
    {
    }
}

} 

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            (n % 10) + Self::digit_sum(n / 10)
        }
    }

    pub open spec fn digit_product(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            1
        } else {
            (n % 10) * Self::digit_product(n / 10)
        }
    }

    pub open spec fn check_divisibility_spec(n: nat) -> bool {
        let d = Self::digit_sum(n) + Self::digit_product(n);
        d > 0 && n % d == 0
    }

    pub fn check_divisibility(n: i32) -> (result: bool)
        requires
            1 <= n <= 1_000_000,
        ensures
            result == Self::check_divisibility_spec(n as nat),
    {
    }
}

}

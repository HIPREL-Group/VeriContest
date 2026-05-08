use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_of_digits(n: nat) -> nat
        decreases n,
    {
        if n < 10 {
            n
        } else {
            (n % 10) + Self::sum_of_digits(n / 10)
        }
    }

    pub open spec fn digit_root_recursive(n: nat) -> nat
        decreases n,
    {
        if n < 10 {
            n
        } else {
            Self::digit_root_recursive(Self::sum_of_digits(n))
        }
    }

    pub fn add_digits(n: i32) -> (result: i32)
        requires
            0 <= n <= i32::MAX,
        ensures
            result == Self::digit_root_recursive(n as nat),
            0 <= result <= 9,
    {
    }
}

} 

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum_spec(n: nat) -> nat {
        (n / 1000) + ((n / 100) % 10) + ((n / 10) % 10) + (n % 10)
    }

    pub open spec fn is_even_digit_sum(n: nat) -> bool {
        Self::digit_sum_spec(n) % 2 == 0
    }

    pub open spec fn count_even_up_to(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::count_even_up_to((n - 1) as nat)
                + if Self::is_even_digit_sum(n) { 1nat } else { 0nat }
        }
    }

    fn digit_sum(x: i32) -> (result: i32)
        requires
            1 <= x <= 1000,
        ensures
            result as nat == Self::digit_sum_spec(x as nat),
            0 <= result,
    {
    }

    fn even_contrib(x: i32) -> (result: i32)
        requires
            1 <= x <= 1000,
        ensures
            result as nat == if Self::is_even_digit_sum(x as nat) { 1nat } else { 0nat },
            0 <= result <= 1,
    {
    }

    pub fn count_even(num: i32) -> (result: i32)
        requires
            1 <= num <= 1000,
        ensures
            result as nat == Self::count_even_up_to(num as nat),
            0 <= result <= num,
    {
    }
}

}

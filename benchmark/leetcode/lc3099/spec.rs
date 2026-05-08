use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: nat) -> nat
        decreases n,
    {
        if n < 10 {
            n
        } else {
            (n % 10) + Self::digit_sum(n / 10)
        }
    }

    pub fn sum_of_the_digits_of_harshad_number(x: i32) -> (res: i32)
        requires
            1 <= x <= 100,
        ensures
            Self::digit_sum(x as nat) > 0,
            x as nat % Self::digit_sum(x as nat) == 0 ==> res == Self::digit_sum(x as nat),
            x as nat % Self::digit_sum(x as nat) != 0 ==> res == -1i32,
    {
    }
}

}

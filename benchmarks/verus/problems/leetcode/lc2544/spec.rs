use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_count_10(n: int) -> nat
        recommends
            1 <= n <= 1_000_000_000,
    {
        if n >= 1_000_000_000 {
            10
        } else if n >= 100_000_000 {
            9
        } else if n >= 10_000_000 {
            8
        } else if n >= 1_000_000 {
            7
        } else if n >= 100_000 {
            6
        } else if n >= 10_000 {
            5
        } else if n >= 1_000 {
            4
        } else if n >= 100 {
            3
        } else if n >= 10 {
            2
        } else {
            1
        }
    }

    pub open spec fn alternating_suffix_sum(rem: nat, digits: nat, sign: int) -> int
        decreases digits,
    {
        if digits == 0 {
            0
        } else {
            sign * (rem % 10) as int
                + Self::alternating_suffix_sum(rem / 10, (digits - 1) as nat, -sign)
        }
    }

    pub open spec fn alternating_digit_sum_spec(n: nat) -> int
        recommends
            1 <= n <= 1_000_000_000,
    {
        let d = Self::digit_count_10(n as int);
        let s = if d % 2 == 0 { -1 } else { 1 };
        Self::alternating_suffix_sum(n, d, s)
    }

    pub fn alternate_digit_sum(n: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result as int == Self::alternating_digit_sum_spec(n as nat),
    {
    }
}

}

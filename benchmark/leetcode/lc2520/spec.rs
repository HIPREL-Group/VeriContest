use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn has_no_zero_digits(n: nat) -> bool
        decreases n,
    {
        if n == 0 {
            true
        } else {
            n % 10 != 0 && Self::has_no_zero_digits(n / 10)
        }
    }

    pub open spec fn digit_contrib_spec(orig: nat, digit: nat) -> nat {
        if digit == 0 {
            0
        } else if orig % digit == 0 {
            1
        } else {
            0
        }
    }

    pub open spec fn count_digits_bounded(orig: nat, rem: nat, digits: nat) -> nat
        decreases digits,
    {
        if digits == 0 {
            0
        } else {
            Self::digit_contrib_spec(orig, rem % 10)
                + Self::count_digits_bounded(orig, rem / 10, (digits - 1) as nat)
        }
    }

    pub open spec fn count_digits_spec(num: nat) -> nat {
        Self::count_digits_bounded(num, num, 10)
    }

    fn digit_contrib(orig: u128, digit: u128) -> (result: i32)
        ensures
            result as nat == Self::digit_contrib_spec(orig as nat, digit as nat),
            0 <= result <= 1,
    {
        
    }

    pub fn count_digits(num: i32) -> (result: i32)
        requires
            1 <= num <= 1_000_000_000,
            Self::has_no_zero_digits(num as nat),
        ensures
            result as nat == Self::count_digits_spec(num as nat),
            0 <= result <= 10,
    {
        
    }
}

} 

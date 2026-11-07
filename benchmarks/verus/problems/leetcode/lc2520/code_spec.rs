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
        if digit == 0 {
            0
        } else if orig % digit == 0 {
            1
        } else {
            0
        }
    }

    pub fn count_digits(num: i32) -> (result: i32)
        requires
            1 <= num <= 1_000_000_000,
            Self::has_no_zero_digits(num as nat),
        ensures
            result as nat == Self::count_digits_spec(num as nat),
            0 <= result <= 10,
    {
        let orig = num as u128;
        let mut rem = orig;
        let mut digits: u8 = 10;
        let mut count: i32 = 0;
        while digits > 0
        {
            let old_count = count;
            let old_digits = digits;
            let old_rem = rem;
            let digit = rem % 10;
            let add = Self::digit_contrib(orig, digit);
            count = count + add;
            rem = rem / 10;
            digits = digits - 1;
        }
        count
    }
}

} 

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sq_spec(d: nat) -> nat {
        if d == 0 {
            0
        } else if d == 1 {
            1
        } else if d == 2 {
            4
        } else if d == 3 {
            9
        } else if d == 4 {
            16
        } else if d == 5 {
            25
        } else if d == 6 {
            36
        } else if d == 7 {
            49
        } else if d == 8 {
            64
        } else {
            81
        }
    }

    pub fn digit_sq(d: u128) -> (res: u128)
        ensures
            res as nat == Self::digit_sq_spec(d as nat),
            res <= 81,
    {
        
    }

    pub open spec fn next_spec_bounded(n: nat, digits: nat) -> nat
        decreases digits,
    {
        if digits == 0 {
            0
        } else {
            Self::digit_sq_spec(n % 10) + Self::next_spec_bounded(n / 10, (digits - 1) as nat)
        }
    }

    pub open spec fn next_spec(n: nat) -> nat {
        Self::next_spec_bounded(n, 10)
    }

    pub open spec fn iterate_next(n: nat, steps: nat) -> nat
        decreases steps,
    {
        if steps == 0 {
            n
        } else {
            Self::next_spec(Self::iterate_next(n, (steps - 1) as nat))
        }
    }

    pub open spec fn happy_within(n: nat, limit: nat) -> bool {
        Self::iterate_next(n, limit) == 1
    }

    fn next_num(x: u128) -> (res: u128)
        ensures
            res as nat == Self::next_spec(x as nat),
            res <= 810,
    {
        
    }

    pub fn is_happy(n: i32) -> (res: bool)
        requires
            1 <= n <= i32::MAX,
        ensures
            res == Self::happy_within(n as nat, 1000),
    {
        
    }
}

}

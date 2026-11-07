use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

pub struct Solution;

impl Solution {
    pub open spec fn first_wins_count(a: int, b: int, x: int) -> nat
        decreases 7 - x,
    {
        if x > 6 {
            0nat
        } else {
            (if abs_diff(a, x) < abs_diff(b, x) {
                1nat
            } else {
                0nat
            }) + Self::first_wins_count(a, b, x + 1)
        }
    }

    pub open spec fn draws_count(a: int, b: int, x: int) -> nat
        decreases 7 - x,
    {
        if x > 6 {
            0nat
        } else {
            (if abs_diff(a, x) == abs_diff(b, x) {
                1nat
            } else {
                0nat
            }) + Self::draws_count(a, b, x + 1)
        }
    }

    pub open spec fn second_wins_count(a: int, b: int, x: int) -> nat
        decreases 7 - x,
    {
        if x > 6 {
            0nat
        } else {
            (if abs_diff(a, x) > abs_diff(b, x) {
                1nat
            } else {
                0nat
            }) + Self::second_wins_count(a, b, x + 1)
        }
    }

    pub fn dice_outcomes(a: i32, b: i32) -> (result: (i32, i32, i32))
        requires
            1 <= a <= 6,
            1 <= b <= 6,
        ensures
            result.0 as int == Self::first_wins_count(a as int, b as int, 1),
            result.1 as int == Self::draws_count(a as int, b as int, 1),
            result.2 as int == Self::second_wins_count(a as int, b as int, 1),
            result.0 + result.1 + result.2 == 6,
    {
    }
}

}

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
        let mut first_wins: i32 = 0;
        let mut draws: i32 = 0;
        let mut second_wins: i32 = 0;
        let mut x: i32 = 1;
        while x <= 6 {
            let da = if a >= x { a - x } else { x - a };
            let db = if b >= x { b - x } else { x - b };
            if da < db {
                first_wins = first_wins + 1;
            } else if da == db {
                draws = draws + 1;
            } else {
                second_wins = second_wins + 1;
            }
            x = x + 1;
        }
        (first_wins, draws, second_wins)
    }
}

}

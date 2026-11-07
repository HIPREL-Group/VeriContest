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

    proof fn lemma_counts_sum(a: int, b: int, x: int)
        requires 1 <= x <= 7,
        ensures
            Self::first_wins_count(a, b, x) + Self::draws_count(a, b, x)
                + Self::second_wins_count(a, b, x) == 7 - x,
        decreases 7 - x,
    {
        if x < 7 {
            Self::lemma_counts_sum(a, b, x + 1);
        }
    }

    proof fn lemma_first_wins_step(a: int, b: int, x: int)
        requires 1 <= x <= 6,
        ensures
            Self::first_wins_count(a, b, x) == Self::first_wins_count(a, b, x + 1)
                + (if abs_diff(a, x) < abs_diff(b, x) { 1nat } else { 0nat }),
    {
    }

    proof fn lemma_draws_step(a: int, b: int, x: int)
        requires 1 <= x <= 6,
        ensures
            Self::draws_count(a, b, x) == Self::draws_count(a, b, x + 1)
                + (if abs_diff(a, x) == abs_diff(b, x) { 1nat } else { 0nat }),
    {
    }

    proof fn lemma_second_wins_step(a: int, b: int, x: int)
        requires 1 <= x <= 6,
        ensures
            Self::second_wins_count(a, b, x) == Self::second_wins_count(a, b, x + 1)
                + (if abs_diff(a, x) > abs_diff(b, x) { 1nat } else { 0nat }),
    {
    }

    proof fn lemma_sub_bounds(x: int, a: int)
        requires 1 <= x <= 6, 1 <= a <= 6,
        ensures -5 <= x - a <= 5,
    {
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
        while x <= 6
            invariant
                1 <= a <= 6,
                1 <= b <= 6,
                1 <= x <= 7,
                0 <= first_wins <= 6,
                0 <= draws <= 6,
                0 <= second_wins <= 6,
                first_wins as int == Self::first_wins_count(a as int, b as int, 1)
                    - Self::first_wins_count(a as int, b as int, x as int),
                draws as int == Self::draws_count(a as int, b as int, 1)
                    - Self::draws_count(a as int, b as int, x as int),
                second_wins as int == Self::second_wins_count(a as int, b as int, 1)
                    - Self::second_wins_count(a as int, b as int, x as int),
                first_wins + draws + second_wins == x - 1,
            decreases 7 - x,
        {
            proof {
                Self::lemma_sub_bounds(x as int, a as int);
                Self::lemma_sub_bounds(x as int, b as int);
            }
            let da = if a >= x { a - x } else { x - a };
            let db = if b >= x { b - x } else { x - b };
            if da < db {
                proof {
                    Self::lemma_first_wins_step(a as int, b as int, x as int);
                }
                first_wins = first_wins + 1;
            } else if da == db {
                proof {
                    Self::lemma_draws_step(a as int, b as int, x as int);
                }
                draws = draws + 1;
            } else {
                proof {
                    Self::lemma_second_wins_step(a as int, b as int, x as int);
                }
                second_wins = second_wins + 1;
            }
            x = x + 1;
        }
        proof {
            Self::lemma_counts_sum(a as int, b as int, 7);
        }
        (first_wins, draws, second_wins)
    }
}

}

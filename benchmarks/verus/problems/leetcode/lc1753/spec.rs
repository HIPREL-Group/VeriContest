use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max3(a: int, b: int, c: int) -> int {
        if a >= b && a >= c {
            a
        } else if b >= c {
            b
        } else {
            c
        }
    }

    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn max_score_spec(a: int, b: int, c: int) -> int {
        Self::spec_min((a + b + c) / 2, a + b + c - Self::spec_max3(a, b, c))
    }

    pub fn maximum_score(a: i32, b: i32, c: i32) -> (res: i32)
        requires
            1 <= a <= 100_000,
            1 <= b <= 100_000,
            1 <= c <= 100_000,
        ensures
            res == Self::max_score_spec(a as int, b as int, c as int),
    {
    }
}

}

use vstd::arithmetic::power::{lemma_square_is_pow2, pow};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn judge_square_sum_spec(c: int) -> bool {
        exists|a: nat, b: nat| pow(a as int, 2) + pow(b as int, 2) == c
    }

    pub fn judge_square_sum(c: i32) -> bool
        requires
            0 <= c,
        returns
            Self::judge_square_sum_spec(c as int),
    {
    }
}

}

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
        let c64: i64 = c as i64;

        let mut lo: i64 = 0;
        let mut hi: i64 = if c64 <= 46340 { c64 } else { 46340 };
        while lo <= hi
        {
            let mid: i64 = lo + (hi - lo) / 2;
            let sq: i64 = mid * mid;
            if sq <= c64 {
                lo = mid + 1;
            } else {
                hi = mid - 1;
            }
        }
        let right_init: i64 = hi;

        let mut left: i64 = 0;
        let mut right: i64 = right_init;

        while left <= right
        {
            let sum: i64 = left * left + right * right;
            if sum == c64 {
                return true;
            }
            if sum < c64 {
                left += 1;
            } else {
                right -= 1;
            }
        }
        false
    }
}

}

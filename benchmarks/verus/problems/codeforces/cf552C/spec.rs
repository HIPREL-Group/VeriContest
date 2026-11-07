use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn coeffs_valid(coeffs: Seq<int>) -> bool {
        forall |i: int| 0 <= i < coeffs.len() ==> -1 <= #[trigger] coeffs[i] <= 1
    }

    pub open spec fn weighted_sum_of_powers(w: int, coeffs: Seq<int>) -> int
        recommends
            2 <= w,
        decreases coeffs.len(),
    {
        if coeffs.len() == 0 {
            0
        } else {
            coeffs[0] + w * Self::weighted_sum_of_powers(w, coeffs.subrange(1, coeffs.len() as int))
        }
    }

    pub open spec fn exists_representation(w: int, m: int, digits: int) -> bool
        recommends
            2 <= w,
            0 <= digits,
    {
        exists |coeffs: Seq<int>| coeffs.len() <= digits
            && Self::coeffs_valid(coeffs)
            && Self::weighted_sum_of_powers(w, coeffs) == m
    }

    pub fn can_balance(w: i64, m: i64) -> (result: bool)
        requires
            2 <= w <= 1_000_000_000,
            1 <= m <= 1_000_000_000,
        ensures
            result == Self::exists_representation(w as int, m as int, 31),
    {
    }
}

}

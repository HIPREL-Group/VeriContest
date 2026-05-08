use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_pow(base: int, exp: nat) -> int
        decreases exp,
    {
        if exp == 0 {
            1
        } else {
            base * Self::spec_pow(base, (exp - 1) as nat)
        }
    }

    pub fn poor_pigs(buckets: i32, minutes_to_die: i32, minutes_to_test: i32) -> (result: i32)
        requires
            1 <= buckets <= 1000,
            1 <= minutes_to_die <= minutes_to_test <= 100,
            1 <= minutes_to_test as int / minutes_to_die as int,
        ensures
            0 <= result,
            Self::spec_pow((minutes_to_test as int / minutes_to_die as int) + 1, result as nat) >= buckets as int,
            forall |r: int| 0 <= r < result as int ==> (#[trigger] Self::spec_pow((minutes_to_test as int / minutes_to_die as int) + 1, r as nat)) < buckets as int,
    {
    }
}

}

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
        let states = minutes_to_test / minutes_to_die + 1;
        let mut pigs: i32 = 0;
        let mut capacity: i32 = 1;
        while capacity < buckets {
            let prod: i64 = capacity as i64 * states as i64;
            capacity = prod as i32;
            pigs += 1;
        }
        pigs
    }
}

}

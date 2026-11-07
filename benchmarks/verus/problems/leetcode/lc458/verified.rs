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

        while capacity < buckets
            invariant
                1 <= buckets <= 1000,
                1 <= minutes_to_die <= minutes_to_test <= 100,
                1 <= minutes_to_test as int / minutes_to_die as int,
                states == minutes_to_test / minutes_to_die + 1,
                2 <= states <= 101,
                0 <= pigs,
                capacity >= 1,
                pigs as int <= capacity as int,
                capacity as int == Self::spec_pow(states as int, pigs as nat),
                forall |r: int| 0 <= r < pigs as int ==> (#[trigger] Self::spec_pow(states as int, r as nat)) < buckets as int,
            decreases buckets - capacity + i32::MAX,
        {
            let old_capacity = capacity;
            let ghost old_pigs = pigs;
            proof {
                assert(old_capacity as int == Self::spec_pow(states as int, old_pigs as nat));
                assert(Self::spec_pow(states as int, pigs as nat) < buckets as int);
                assert(old_capacity <= 999) by (nonlinear_arith)
                    requires
                        old_capacity < buckets,
                        buckets <= 1000,
                {
                }
                assert(0 <= old_capacity as int * states as int <= 100899) by (nonlinear_arith)
                    requires
                        0 <= old_capacity <= 999,
                        0 <= states <= 101,
                {
                }
            }
            let prod: i64 = old_capacity as i64 * states as i64;
            assert(prod as int == old_capacity as int * states as int);
            assert(0 <= prod <= 100899);
            capacity = prod as i32;
            assert(capacity as int == prod as int);
            pigs += 1;
            proof {
                assert(pigs == old_pigs + 1);
                assert(Self::spec_pow(states as int, pigs as nat)
                    == states as int * Self::spec_pow(states as int, old_pigs as nat));
                assert(capacity as int == old_capacity as int * states as int);
                assert(capacity as int == Self::spec_pow(states as int, pigs as nat));
                assert(Self::spec_pow(states as int, old_pigs as nat) < buckets as int);
                assert forall |r: int| 0 <= r < pigs as int implies (#[trigger] Self::spec_pow(states as int, r as nat)) < buckets as int by {
                    if r < old_pigs as int {
                    } else {
                        assert(r == old_pigs as int);
                    }
                }
                assert(old_pigs as int + 1 <= old_capacity as int + 1);
                assert(old_capacity as int + 1 <= old_capacity as int * states as int) by (nonlinear_arith)
                    requires
                        old_capacity >= 1,
                        states >= 2,
                {
                }
                assert(pigs as int <= capacity as int);
            }
        }

        proof {
            assert(!(capacity < buckets));
            assert(capacity as int >= buckets as int);
            assert(Self::spec_pow(states as int, pigs as nat) >= buckets as int);
        }

        pigs
    }
}

}

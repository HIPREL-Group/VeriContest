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

    fn mul_small(a: i32, b: i32) -> (r: i32)
        requires
            0 <= a <= 999,
            0 <= b <= 101,
        ensures
            r as int == a as int * b as int,
    {
        let mut acc: i32 = 0;
        let mut t: i32 = 0;
        while t < b
            invariant
                0 <= a <= 999,
                0 <= b <= 101,
                0 <= t <= b,
                acc as int == a as int * t as int,
                0 <= acc <= 100899,
            decreases b - t,
        {
            proof {
                assert(t + 1 <= b);
                assert(0 <= t + 1 <= 101);
                assert(a as int * (t as int + 1) <= 100899) by (nonlinear_arith)
                    requires
                        0 <= a <= 999,
                        0 <= t + 1 <= 101,
                {
                }
                assert(acc as int + a as int == a as int * (t as int + 1)) by (nonlinear_arith)
                    requires
                        acc as int == a as int * t as int,
                {
                }
                assert(acc as int + a as int <= 100899);
            }
            acc += a;
            t += 1;
        }
        acc
    }

    #[verifier::exec_allows_no_decreases_clause]
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
        {
            let old_capacity = capacity;
            let old_pigs = pigs;
            proof {
                assert(old_capacity as int == Self::spec_pow(states as int, old_pigs as nat));
                assert(Self::spec_pow(states as int, pigs as nat) < buckets as int);
                assert(old_capacity <= 999) by (nonlinear_arith)
                    requires
                        old_capacity < buckets,
                        buckets <= 1000,
                {
                }
            }
            capacity = Self::mul_small(old_capacity, states);
            pigs += 1;
            proof {
                assert(pigs == old_pigs + 1);
                assert(Self::spec_pow(states as int, pigs as nat)
                    == states as int * Self::spec_pow(states as int, old_pigs as nat));
                assert(capacity as int == old_capacity as int * states as int);
                assert(capacity as int == Self::spec_pow(states as int, pigs as nat));
                // The old invariant gives us forall r < old_pigs: spec_pow < buckets
                // We also know spec_pow(states, old_pigs) < buckets (from capacity < buckets before update)
                // So forall r < pigs (= old_pigs + 1): spec_pow < buckets
                assert(Self::spec_pow(states as int, old_pigs as nat) < buckets as int);
                assert forall |r: int| 0 <= r < pigs as int implies (#[trigger] Self::spec_pow(states as int, r as nat)) < buckets as int by {
                    if r < old_pigs as int {
                        // from old invariant
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

#[cfg(any())]
impl Solution {
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

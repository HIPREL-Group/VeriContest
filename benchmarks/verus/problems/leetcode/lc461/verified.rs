use vstd::arithmetic::logarithm::{
    lemma_log0, lemma_log_is_ordered, lemma_log_nonnegative, lemma_log_pow, lemma_log_s, log,
};
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2, pow2};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn popcnt_spec_helper(x: nat, acc: nat) -> nat
        decreases x,
    {
        if x == 0 {
            acc
        } else {
            let ones = x % 2;
            let new_acc = acc + ones;
            Solution::popcnt_spec_helper(x / 2, new_acc)
        }
    }

    pub proof fn lemma_xor_nonneg(a: i32, b: i32)
        requires
            0 <= a <= i32::MAX,
            0 <= b <= i32::MAX,
        ensures
            (a ^ b) >= 0,
    {
        assert(a ^ b >= 0) by(bit_vector)
            requires
                0 <= a <= i32::MAX,
                0 <= b <= i32::MAX;
    }
    pub open spec fn popcnt_spec(x: nat) -> nat {
        Solution::popcnt_spec_helper(x, 0)
    }

    pub proof fn popcnt_bound(x: nat, a: nat)
        ensures
            Solution::popcnt_spec_helper(x, a) <= a + log(2, x as int) + 1,
        decreases x,
    {
        Solution::popcnt_properties(x, a);
        if x < 2 {
            lemma_log0(2, x as int);
        } else {
            lemma_log_s(2, x as int);
            lemma_log_nonnegative(2, (x / 2) as int);
            Solution::popcnt_bound(x / 2, a + (x % 2));
        }
    }

    pub proof fn popcnt_bound_i32(x: nat)
        requires
            x <= pow2(31),
        ensures
            Solution::popcnt_spec(x) <= 32,
    {
        lemma_pow2(31);
        lemma_log_pow(2, 31);
        lemma_log_is_ordered(2, x as int, pow2(31) as int);
        Solution::popcnt_bound(x, 0);
    }

    pub proof fn popcnt_properties(x: nat, a: nat)
        ensures
            Solution::popcnt_spec_helper(x, a) == Solution::popcnt_spec_helper(x / 2, a + (x % 2)),
            Solution::popcnt_spec_helper(x, a) >= a,
        decreases x,
    {
        if x == 0 {
        } else {
            let ones = x % 2;
            let new_acc = a + ones;

            Solution::popcnt_properties(x / 2, new_acc);
        }
    }

    pub fn hamming_distance(x: i32, y: i32) -> (res: i32)
        requires
            0 <= x <= i32::MAX,
            0 <= y <= i32::MAX,
        ensures
            res == Solution::popcnt_spec((x ^ y) as nat),
    {
        proof {
            Self::lemma_xor_nonneg(x, y);
            lemma2_to64();
            Solution::popcnt_bound_i32((x ^ y) as nat);
        }
        let mut xor = (x ^ y) as u32;
        let mut count: u32 = 0;
        while xor != 0
            invariant
                0 <= x <= i32::MAX,
                0 <= y <= i32::MAX,
                (x ^ y) >= 0,
                Solution::popcnt_spec_helper(xor as nat, count as nat) == Solution::popcnt_spec(
                    (x ^ y) as nat,
                ),
            decreases xor,
        {
            proof {
                lemma2_to64();
                Solution::popcnt_bound_i32((x ^ y) as nat);
                Solution::popcnt_properties(xor as nat, count as nat);
            }
            count += xor % 2;
            xor /= 2;
        }
        count as i32
    }
}

} 

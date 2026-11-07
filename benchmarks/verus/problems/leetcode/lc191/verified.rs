use vstd::arithmetic::logarithm::{lemma_log0, lemma_log_is_ordered, lemma_log_pow, lemma_log_s, log};
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
            Solution::popcnt_bound(x / 2, a + (x % 2));
            lemma_log_s(2, x as int);
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

    pub fn hamming_weight(n: i32) -> (res: i32)
        requires
            1 <= n <= i32::MAX,
        ensures
            res == Solution::popcnt_spec(n as nat),
    {
        let mut acc: u32 = 0;
        let mut nmut = n as u32;
        proof {
            lemma2_to64();
            Solution::popcnt_bound_i32(n as nat);
        }
        while (nmut != 0)
            invariant
                1 <= n <= pow2(31) - 1,
                Solution::popcnt_spec_helper(nmut as nat, acc as nat) == Solution::popcnt_spec(
                    n as nat,
                ),
            decreases nmut,
        {
            proof {
                Solution::popcnt_bound_i32(n as nat);
                Solution::popcnt_properties(nmut as nat, acc as nat);
            }
            acc += nmut % 2;
            nmut /= 2;
        }
        acc as i32
    }
}

} 

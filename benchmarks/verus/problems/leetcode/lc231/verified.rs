use vstd::arithmetic::{
    div_mod::lemma_fundamental_div_mod,
    logarithm::{lemma_log0, lemma_log_nonnegative, lemma_log_s, log},
    power::{lemma_pow0, pow},
    power2::{lemma_pow2, lemma_pow2_unfold, pow2},
};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_power_of_two(n: int) -> bool {
        if n <= 0 {
            false
        } else {
            pow2(log(2, n) as nat) == n
        }
    }

    pub fn is_power_of_two(n: i32) -> (result: bool)
        requires
            -2_147_483_648 <= n <= 2_147_483_647,
        ensures
            result == Self::spec_is_power_of_two(n as int),
    {
        if n <= 0 {
            false
        } else {
            let mut x = n;
            while x > 1 && x % 2 == 0
                invariant
                    x > 0,
                    Self::spec_is_power_of_two(n as int) == Self::spec_is_power_of_two(
                        x as int,
                    ),
                decreases x,
            {
                proof {
                    let old_x = x as int;
                    let new_x = old_x / 2;
                    lemma_fundamental_div_mod(old_x, 2);
                    lemma_log_s(2, old_x);
                    lemma_log_nonnegative(2, new_x);
                    lemma_pow2_unfold(log(2, old_x) as nat);
                }
                x = x / 2;
            }
            proof {
                if x == 1 {
                    lemma_log0(2, 1 as int);
                    lemma_pow2(0 as nat);
                    lemma_pow0(2);
                } else {
                    if Self::spec_is_power_of_two(x as int) {
                        let k = log(2, x as int) as nat;
                        lemma_pow2(0 as nat);
                        lemma_pow0(2);
                        lemma_pow2_unfold(k);
                    }
                }
            }
            x == 1
        }
    }
}

} 

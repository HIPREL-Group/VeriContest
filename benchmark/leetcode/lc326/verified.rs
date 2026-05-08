use vstd::arithmetic::{
    div_mod::lemma_fundamental_div_mod,
    logarithm::{lemma_log0, lemma_log_nonnegative, lemma_log_s, log},
    power::{lemma_pow0, pow},
};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_power_of_three(n: int) -> bool {
        if n <= 0 {
            false
        } else {
            pow(3, log(3, n) as nat) == n
        }
    }

    pub fn is_power_of_three(n: i32) -> (res: bool)
        requires
            -2_147_483_648 <= n <= 2_147_483_647,
        ensures
            res == Self::spec_is_power_of_three(n as int),
    {
        if n <= 0 {
            false
        } else {
            let mut x = n;
            while x > 1 && x % 3 == 0
                invariant
                    x > 0,
                    Self::spec_is_power_of_three(n as int) == Self::spec_is_power_of_three(
                        x as int,
                    ),
                decreases x,
            {
                proof {
                    let old_x = x as int;
                    let new_x = old_x / 3;
                    lemma_fundamental_div_mod(old_x, 3);
                    lemma_log_s(3, old_x);
                    lemma_log_nonnegative(3, new_x);
                    reveal(pow);
                }
                x = x / 3;
            }
            proof {
                if x == 1 {
                    lemma_log0(3, 1 as int);
                    lemma_pow0(3);
                } else {
                    if Self::spec_is_power_of_three(x as int) {
                        let k = log(3, x as int) as nat;
                        lemma_pow0(3);
                        reveal(pow);
                    }
                }
            }
            x == 1
        }
    }
}

} 

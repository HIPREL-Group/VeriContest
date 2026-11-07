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
    pub open spec fn spec_is_power_of_four(n: int) -> bool {
        if n <= 0 {
            false
        } else {
            pow(4, log(4, n) as nat) == n
        }
    }

    pub fn is_power_of_four(n: i32) -> (res: bool)
        requires
            -2_147_483_648 <= n <= 2_147_483_647,
        ensures
            res == Self::spec_is_power_of_four(n as int),
    {
        if n <= 0 {
            false
        } else {
            let mut x = n;
            while x > 1 && x % 4 == 0
                invariant
                    x > 0,
                    Self::spec_is_power_of_four(n as int) == Self::spec_is_power_of_four(
                        x as int,
                    ),
                decreases x,
            {
                proof {
                    let old_x = x as int;
                    let new_x = old_x / 4;
                    lemma_fundamental_div_mod(old_x, 4);
                    lemma_log_s(4, old_x);
                    lemma_log_nonnegative(4, new_x);
                    reveal(pow);
                }
                x = x / 4;
            }
            proof {
                if x == 1 {
                    lemma_log0(4, 1 as int);
                    lemma_pow0(4);
                } else {
                    
                    if Self::spec_is_power_of_four(x as int) {
                        let k = log(4, x as int) as nat;
                        lemma_pow0(4);
                        
                        reveal(pow);
                        
                    }
                }
            }
            x == 1
        }
    }
}

} 

use vstd::arithmetic::div_mod::{
    lemma_mod_bound, lemma_mod_decreases, lemma_mod_equivalence, lemma_mod_is_zero,
    lemma_mod_multiples_basic, lemma_mod_multiples_vanish, lemma_mod_twice,
};
use vstd::arithmetic::logarithm::{lemma_log0, lemma_log_is_ordered, lemma_log_pow, log};
use vstd::arithmetic::mul::{
    lemma_mul_by_zero_is_zero, lemma_mul_increases, lemma_mul_is_distributive_add_other_way,
};
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2, pow2};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pass_the_pillow_spec_inner(n: nat, time: nat, pos: nat, dir: bool) -> nat
        decreases time,
    {
        if time == 0 {
            pos
        } else {
            let dir = if pos == 1 {
                true
            } else if pos == n {
                false
            } else {
                dir
            };
            Self::pass_the_pillow_spec_inner(
                n,
                (time - 1) as nat,
                (pos + if dir {
                    1
                } else {
                    -1
                }) as nat,
                dir,
            )
        }
    }

    pub open spec fn pass_the_pillow_spec(n: nat, time: nat) -> nat {
        Self::pass_the_pillow_spec_inner(n, time, 1, true)
    }

    pub fn pass_the_pillow(n: i32, time: i32) -> (res: i32)
        requires
            2 <= n <= 1000,
            1 <= time <= 1000,
        ensures
            res == Self::pass_the_pillow_spec(n as nat, time as nat) as i32,
    {
    }
}

} 

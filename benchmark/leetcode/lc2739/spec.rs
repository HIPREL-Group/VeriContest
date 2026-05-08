use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const KM_PER_LITER: i32 = 10;

    pub spec const KM_PER_LITER_SPEC: nat = (Self::KM_PER_LITER as nat);

    pub open spec fn distance_traveled_spec(main_tank: nat, additional_tank: nat) -> nat
        decreases main_tank,
    {
        if main_tank < 5 || additional_tank == 0 {
            main_tank * Self::KM_PER_LITER_SPEC
        } else {
            5 * Self::KM_PER_LITER_SPEC + Self::distance_traveled_spec(
                (main_tank - 4) as nat,
                (additional_tank - 1) as nat,
            )
        }
    }

    pub fn distance_traveled(main_tank: i32, additional_tank: i32) -> (res: i32)
        requires
            0 <= main_tank <= 100,
            0 <= additional_tank <= 100,
        ensures
            res == Self::distance_traveled_spec(main_tank as nat, additional_tank as nat) as i32,
    {
    }
}

} 

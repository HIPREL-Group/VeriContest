use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bit_length_spec(n: nat) -> nat
        decreases n,
    {
        if n <= 1 { 1 } else { 1 + Solution::bit_length_spec(n / 2) }
    }

    pub open spec fn bitwise_complement_spec(num: nat) -> nat {
        (pow2(Solution::bit_length_spec(num)) - 1 - num) as nat
    }

    pub fn find_complement_nonzero(num: i32) -> (res: i32)
        requires
            1 <= num <= i32::MAX,
        ensures
            res == Solution::bitwise_complement_spec(num as nat),
    {
        let n = num as u32;
        let mut mask: u32 = 1;
        while mask <= n {
            let old_mask = mask;
            mask = mask * 2;
        }
        (mask - 1 - n) as i32
    }

    pub fn bitwise_complement(n: i32) -> (res: i32)
        requires
            0 <= n < 1000000000,
        ensures
            res == Solution::bitwise_complement_spec(n as nat),
    {
        if n == 0 {
            return 1;
        }
        Self::find_complement_nonzero(n)
    }
}

} 

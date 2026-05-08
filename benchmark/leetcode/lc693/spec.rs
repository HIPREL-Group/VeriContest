use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn has_alt_bits_spec(n: u32) -> bool {
        let x: u32 = n ^ (n >> 1u32);
        (x & ((x as int + 1) as u32)) == 0u32
    }

    pub fn has_alternating_bits(n: i32) -> (result: bool)
        requires
            1 <= n < i32::MAX,
        ensures
            result == Solution::has_alt_bits_spec(n as u32),
    {
    }
}

} 

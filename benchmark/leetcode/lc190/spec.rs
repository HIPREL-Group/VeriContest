use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn get_bit(x: i32, i: u32) -> bool
        recommends
            0 <= i < 32,
    {
        (x >> i) & 1 == 1
    }

    pub fn reverse_bits(n: i32) -> (res: i32)
        requires
            0 <= n <= 2_147_483_646,
            n % 2 == 0,
        ensures
            forall|i: int|
                0 <= i < 32 ==> #[trigger] Solution::get_bit(res, i as u32) == Solution::get_bit(
                    n,
                    (31 - i) as u32,
                ),
    {
    }
}

} 

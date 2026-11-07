use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_all_set_bits(x: int) -> bool {
        x > 0 && exists|k: nat| x == pow2(k) - 1
    }

    pub fn smallest_number(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            n <= result,
            Self::is_all_set_bits(result as int),
            forall|m: int| n as int <= m < result as int ==> !(#[trigger] Self::is_all_set_bits(m)),
    {
    }
}

}

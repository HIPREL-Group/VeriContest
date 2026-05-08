use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn even_bits_spec(n: int) -> int
        recommends
            1 <= n <= 1000,
    {
        (n / 1) % 2 + (n / 4) % 2 + (n / 16) % 2 + (n / 64) % 2 + (n / 256) % 2 + (n / 1024) % 2
    }

    pub open spec fn odd_bits_spec(n: int) -> int
        recommends
            1 <= n <= 1000,
    {
        (n / 2) % 2 + (n / 8) % 2 + (n / 32) % 2 + (n / 128) % 2 + (n / 512) % 2
    }

    pub fn even_odd_bit(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1000,
        ensures
            result@.len() == 2,
            result@[0] as int == Self::even_bits_spec(n as int),
            result@[1] as int == Self::odd_bits_spec(n as int),
    {
    }
}

}

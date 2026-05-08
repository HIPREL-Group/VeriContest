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

    fn bit_value(n: i32, div: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            div > 0,
        ensures
            result as int == ((n as int / div as int) % 2),
    {
        (n / div) % 2
    }

    pub fn even_odd_bit(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1000,
        ensures
            result@.len() == 2,
            result@[0] as int == Self::even_bits_spec(n as int),
            result@[1] as int == Self::odd_bits_spec(n as int),
    {
        let even = Self::bit_value(n, 1) + Self::bit_value(n, 4) + Self::bit_value(n, 16)
            + Self::bit_value(n, 64) + Self::bit_value(n, 256) + Self::bit_value(n, 1024);
        let odd = Self::bit_value(n, 2) + Self::bit_value(n, 8) + Self::bit_value(n, 32)
            + Self::bit_value(n, 128) + Self::bit_value(n, 512);

        let mut result = Vec::new();
        result.push(even);
        result.push(odd);
        result
    }
}

}

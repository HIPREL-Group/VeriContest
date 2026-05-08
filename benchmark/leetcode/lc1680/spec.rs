use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow2(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

pub open spec fn num_bits(n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        1 + num_bits(n / 2)
    }
}

pub open spec fn concat_value(n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        concat_value(n - 1) * pow2(num_bits(n)) + n
    }
}

impl Solution {
    pub fn concatenated_binary(n: i32) -> (result: i32)
        requires
            1 <= n <= 100_000,
        ensures
            0 <= result < 1_000_000_007,
            result as int == concat_value(n as int) % 1_000_000_007,
    {
    }
}

}

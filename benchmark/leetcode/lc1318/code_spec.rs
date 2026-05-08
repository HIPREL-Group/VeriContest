use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn flips_at_bit(a: i32, b: i32, c: i32, i: u32) -> int {
    let bit_a = ((a >> i) & 1i32) as int;
    let bit_b = ((b >> i) & 1i32) as int;
    let bit_c = ((c >> i) & 1i32) as int;
    if bit_c == 0 {
        bit_a + bit_b
    } else if bit_a == 0 && bit_b == 0 {
        1int
    } else {
        0int
    }
}

pub open spec fn total_flips(a: i32, b: i32, c: i32, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        total_flips(a, b, c, n - 1) + flips_at_bit(a, b, c, (n - 1) as u32)
    }
}

impl Solution {
    pub fn min_flips(a: i32, b: i32, c: i32) -> (result: i32)
        requires
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            1 <= c <= 1_000_000_000,
        ensures
            result as int == total_flips(a, b, c, 31),
    {
        let mut flips: i32 = 0;
        let mut i: i32 = 0;
        while i < 31 {
            let bit_a = (a >> (i as u32)) & 1;
            let bit_b = (b >> (i as u32)) & 1;
            let bit_c = (c >> (i as u32)) & 1;
            if bit_c == 0 {
                flips = flips + bit_a + bit_b;
            } else {
                if bit_a == 0 && bit_b == 0 {
                    flips = flips + 1;
                }
            }
            i = i + 1;
        }
        flips
    }
}

} 

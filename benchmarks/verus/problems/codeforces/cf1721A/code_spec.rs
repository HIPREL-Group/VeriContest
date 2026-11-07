use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn letter_mask(a: u8, b: u8, c: u8, d: u8) -> u32 {
        (1u32 << a) | (1u32 << b) | (1u32 << c) | (1u32 << d)
    }

    pub open spec fn popcount_prefix(mask: u32, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0int
        } else {
            let bit = if (mask >> ((k - 1) as u8)) & 1u32 == 0u32 {
                0int
            } else {
                1int
            };
            Self::popcount_prefix(mask, k - 1) + bit
        }
    }

    pub open spec fn distinct_letters(a: u8, b: u8, c: u8, d: u8) -> int {
        Self::popcount_prefix(Self::letter_mask(a, b, c, d), 26)
    }

    pub open spec fn expected_moves(a: u8, b: u8, c: u8, d: u8) -> int {
        let dc = Self::distinct_letters(a, b, c, d);
        if dc == 1 {
            0int
        } else if dc == 2 {
            1int
        } else if dc == 3 {
            2int
        } else {
            3int
        }
    }

    pub fn popcount_mask26(mask: u32) -> (d: i32)
        ensures
            d as int == Self::popcount_prefix(mask, 26),
    {
        let mut d: i32 = 0;
        let mut k: u8 = 0;
        while k < 26 {
            let pre_d = d;
            let bit: i32 = if (mask >> k) & 1u32 == 0u32 {
                0
            } else {
                1
            };
            d = pre_d + bit;
            k = k + 1;
        }
        d
    }

    pub fn min_moves_to_uniform(a: u8, b: u8, c: u8, d: u8) -> (result: i32)
        requires
            a < 26,
            b < 26,
            c < 26,
            d < 26,
        ensures
            result as int == Self::expected_moves(a, b, c, d),
    {
        let mask: u32 = (1u32 << a) | (1u32 << b) | (1u32 << c) | (1u32 << d);
        let distinct_i: i32 = Self::popcount_mask26(mask);
        let r = if distinct_i == 1 {
            0
        } else if distinct_i == 2 {
            1
        } else if distinct_i == 3 {
            2
        } else {
            3
        };
        r
    }
}

}

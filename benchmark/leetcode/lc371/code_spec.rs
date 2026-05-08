use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn encode12_spec(x: int) -> int {
        if x >= 0 { x } else { x + 4096 }
    }

    pub open spec fn decode12_spec(bits: int) -> int {
        if bits <= 0x07FF { bits } else { bits - 4096 }
    }

    pub open spec fn add12_closed(x: u32, y: u32) -> u32 {
        let mask: u32 = 0x0FFFu32;

        let x1 = (x ^ y) & mask;
        let y1 = ((x & y) << 1u32) & mask;

        let x2 = (x1 ^ y1) & mask;
        let y2 = ((x1 & y1) << 1u32) & mask;

        let x3 = (x2 ^ y2) & mask;
        let y3 = ((x2 & y2) << 1u32) & mask;

        let x4 = (x3 ^ y3) & mask;
        let y4 = ((x3 & y3) << 1u32) & mask;

        let x5 = (x4 ^ y4) & mask;
        let y5 = ((x4 & y4) << 1u32) & mask;

        let x6 = (x5 ^ y5) & mask;
        let y6 = ((x5 & y5) << 1u32) & mask;

        let x7 = (x6 ^ y6) & mask;
        let y7 = ((x6 & y6) << 1u32) & mask;

        let x8 = (x7 ^ y7) & mask;
        let y8 = ((x7 & y7) << 1u32) & mask;

        let x9 = (x8 ^ y8) & mask;
        let y9 = ((x8 & y8) << 1u32) & mask;

        let x10 = (x9 ^ y9) & mask;
        let y10 = ((x9 & y9) << 1u32) & mask;

        let x11 = (x10 ^ y10) & mask;
        let y11 = ((x10 & y10) << 1u32) & mask;

        let x12 = (x11 ^ y11) & mask;

        x12
    }

    fn encode12(x: i32) -> (res: u32)
        requires
            -1000 <= x <= 1000,
        ensures
            res <= 0x0FFFu32,
            res as int == Self::encode12_spec(x as int),
    {
        if x >= 0 {
            x as u32
        } else {
            (x + 4096) as u32
        }
    }

    fn decode12(bits: u32) -> (res: i32)
        requires
            bits <= 0x0FFFu32,
        ensures
            res as int == Self::decode12_spec(bits as int),
    {
        if bits <= 0x07FFu32 {
            bits as i32
        } else {
            bits as i32 - 4096
        }
    }

    fn add12_bits(x: u32, y: u32) -> (res: u32)
        requires
            x <= 0x0FFFu32,
            y <= 0x0FFFu32,
        ensures
            res <= 0x0FFFu32,
            res == Self::add12_closed(x, y),
    {
        let mask: u32 = 0x0FFFu32;

        let x1 = (x ^ y) & mask;
        let y1 = ((x & y) << 1u32) & mask;

        let x2 = (x1 ^ y1) & mask;
        let y2 = ((x1 & y1) << 1u32) & mask;

        let x3 = (x2 ^ y2) & mask;
        let y3 = ((x2 & y2) << 1u32) & mask;

        let x4 = (x3 ^ y3) & mask;
        let y4 = ((x3 & y3) << 1u32) & mask;

        let x5 = (x4 ^ y4) & mask;
        let y5 = ((x4 & y4) << 1u32) & mask;

        let x6 = (x5 ^ y5) & mask;
        let y6 = ((x5 & y5) << 1u32) & mask;

        let x7 = (x6 ^ y6) & mask;
        let y7 = ((x6 & y6) << 1u32) & mask;

        let x8 = (x7 ^ y7) & mask;
        let y8 = ((x7 & y7) << 1u32) & mask;

        let x9 = (x8 ^ y8) & mask;
        let y9 = ((x8 & y8) << 1u32) & mask;

        let x10 = (x9 ^ y9) & mask;
        let y10 = ((x9 & y9) << 1u32) & mask;

        let x11 = (x10 ^ y10) & mask;
        let y11 = ((x10 & y10) << 1u32) & mask;

        let x12 = (x11 ^ y11) & mask;

        x12
    }

    pub fn get_sum(a: i32, b: i32) -> (res: i32)
        requires
            -1000 <= a <= 1000,
            -1000 <= b <= 1000,
        ensures
            res as int == a as int + b as int,
    {
        let left = Self::encode12(a);
        let right = Self::encode12(b);
        let bits = Self::add12_bits(left, right);
        let answer = Self::decode12(bits);
        answer
    }
}

}

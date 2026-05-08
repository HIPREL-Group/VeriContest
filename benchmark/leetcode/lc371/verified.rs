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

    proof fn lemma_encode12_sum(a: int, b: int)
        requires
            -1000 <= a <= 1000,
            -1000 <= b <= 1000,
        ensures
            Self::encode12_spec(a + b) == (Self::encode12_spec(a) + Self::encode12_spec(b)) % 4096,
    {
        if a >= 0 {
            if b >= 0 {
                assert(Self::encode12_spec(a) == a);
                assert(Self::encode12_spec(b) == b);
                assert(Self::encode12_spec(a + b) == a + b);
                assert(0 <= a + b < 4096);
            } else {
                assert(Self::encode12_spec(a) == a);
                assert(Self::encode12_spec(b) == b + 4096);
                if a + b >= 0 {
                    assert(Self::encode12_spec(a + b) == a + b);
                    assert(a + (b + 4096) == (a + b) + 4096);
                    assert((a + (b + 4096)) % 4096 == a + b);
                } else {
                    assert(Self::encode12_spec(a + b) == a + b + 4096);
                    assert(a + (b + 4096) == (a + b) + 4096);
                    assert(((a + b) + 4096) % 4096 == (a + b) + 4096);
                }
            }
        } else {
            if b >= 0 {
                assert(Self::encode12_spec(a) == a + 4096);
                assert(Self::encode12_spec(b) == b);
                if a + b >= 0 {
                    assert(Self::encode12_spec(a + b) == a + b);
                    assert((a + 4096 + b) % 4096 == a + b);
                } else {
                    assert(Self::encode12_spec(a + b) == a + b + 4096);
                    assert((a + 4096 + b) % 4096 == a + b + 4096);
                }
            } else {
                assert(Self::encode12_spec(a) == a + 4096);
                assert(Self::encode12_spec(b) == b + 4096);
                assert(Self::encode12_spec(a + b) == a + b + 4096);
                assert((a + 4096 + b + 4096) % 4096 == a + b + 4096);
            }
        }
    }

    proof fn lemma_decode12_inverse(x: int)
        requires
            -2000 <= x <= 2000,
        ensures
            Self::decode12_spec(Self::encode12_spec(x)) == x,
    {
        if x >= 0 {
            assert(Self::encode12_spec(x) == x);
            assert(Self::decode12_spec(Self::encode12_spec(x)) == x);
        } else {
            assert(Self::encode12_spec(x) == x + 4096);
            assert(0x07FF < x + 4096 <= 0x0FFF);
            assert(Self::decode12_spec(Self::encode12_spec(x)) == x + 4096 - 4096);
        }
    }

    proof fn lemma_mask_mod_4096(x: u32)
        ensures
            ((x & 0x0FFFu32) as int) == (x as int % 4096),
    {
        assert(((x & 0x0FFFu32) as int) == (x as int % 4096)) by (bit_vector);
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
            res == (((x + y) as u32) & 0x0FFFu32),
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

        proof {
            assert(x12 == Self::add12_closed(x, y));
            assert(x12 == (((x + y) as u32) & 0x0FFFu32)) by (bit_vector)
                requires
                    mask == 0x0FFFu32,
                    x <= 0x0FFFu32,
                    y <= 0x0FFFu32,
                    x1 == (x ^ y) & mask,
                    y1 == ((x & y) << 1u32) & mask,
                    x2 == (x1 ^ y1) & mask,
                    y2 == ((x1 & y1) << 1u32) & mask,
                    x3 == (x2 ^ y2) & mask,
                    y3 == ((x2 & y2) << 1u32) & mask,
                    x4 == (x3 ^ y3) & mask,
                    y4 == ((x3 & y3) << 1u32) & mask,
                    x5 == (x4 ^ y4) & mask,
                    y5 == ((x4 & y4) << 1u32) & mask,
                    x6 == (x5 ^ y5) & mask,
                    y6 == ((x5 & y5) << 1u32) & mask,
                    x7 == (x6 ^ y6) & mask,
                    y7 == ((x6 & y6) << 1u32) & mask,
                    x8 == (x7 ^ y7) & mask,
                    y8 == ((x7 & y7) << 1u32) & mask,
                    x9 == (x8 ^ y8) & mask,
                    y9 == ((x8 & y8) << 1u32) & mask,
                    x10 == (x9 ^ y9) & mask,
                    y10 == ((x9 & y9) << 1u32) & mask,
                    x11 == (x10 ^ y10) & mask,
                    y11 == ((x10 & y10) << 1u32) & mask,
                    x12 == (x11 ^ y11) & mask,
            {
            }
            assert((((x + y) as u32) & 0x0FFFu32) <= 0x0FFFu32) by (bit_vector);
            assert(x12 <= 0x0FFFu32);
        }

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
        let total = left + right;
        proof {
            Self::lemma_mask_mod_4096(total);
            Self::lemma_encode12_sum(a as int, b as int);
            assert(bits == (total & 0x0FFFu32));
            assert(bits as int == (total as int % 4096));
            assert(bits as int == Self::encode12_spec(a as int + b as int));
        }
        let answer = Self::decode12(bits);
        proof {
            Self::lemma_decode12_inverse(a as int + b as int);
            assert(answer as int == Self::decode12_spec(bits as int));
            assert(answer as int == a as int + b as int);
        }
        answer
    }
}

}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bit_is_one(n: u32, k: int) -> bool {
        0 <= k < 31 && (((n >> (k as u32)) & 1u32) == 1u32)
    }

    pub open spec fn last_one_pos(n: u32, upto: int) -> int
        decreases upto,
    {
        if upto <= 0 {
            -1
        } else if Self::bit_is_one(n, upto - 1) {
            upto - 1
        } else {
            Self::last_one_pos(n, upto - 1)
        }
    }

    pub open spec fn new_gap_at(n: u32, pos: int) -> int {
        let last = Self::last_one_pos(n, pos);
        if last >= 0 { pos - last } else { 0 }
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a > b { a } else { b }
    }

    pub open spec fn binary_gap_prefix(n: u32, upto: int) -> int
        decreases upto,
    {
        if upto <= 0 {
            0
        } else if Self::bit_is_one(n, upto - 1) {
            Self::spec_max(
                Self::binary_gap_prefix(n, upto - 1),
                Self::new_gap_at(n, upto - 1),
            )
        } else {
            Self::binary_gap_prefix(n, upto - 1)
        }
    }

    pub open spec fn binary_gap_spec(n: u32) -> int {
        Self::binary_gap_prefix(n, 31)
    }

    pub fn binary_gap(n: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result as int == Self::binary_gap_spec(n as u32),
    {
        let nu = n as u32;
        let mut m = nu;
        let mut pos: u32 = 0;
        let mut best: u32 = 0;
        let mut last: u32 = 0;
        let mut has_last = false;
        while pos < 31u32 {
            if (m & 1u32) == 1u32 {
                if has_last {
                    let gap = pos - last;
                    if gap > best {
                        best = gap;
                    }
                }
                last = pos;
                has_last = true;
            }
            m = m >> 1u32;
            pos = pos + 1u32;
        }
        best as i32
    }
}

}

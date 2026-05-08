use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn between(x: int, lo: int, hi: int) -> bool {
        (lo < x && x < hi) || (hi < x && x < lo)
    }

    pub open spec fn rook_row_attack(a: int, b: int, c: int, d: int, e: int, f: int) -> bool {
        a == e && !(c == a && Self::between(d, b, f))
    }

    pub open spec fn rook_col_attack(a: int, b: int, c: int, d: int, e: int, f: int) -> bool {
        b == f && !(d == b && Self::between(c, a, e))
    }

    pub open spec fn rook_attack(a: int, b: int, c: int, d: int, e: int, f: int) -> bool {
        Self::rook_row_attack(a, b, c, d, e, f) || Self::rook_col_attack(a, b, c, d, e, f)
    }

    pub open spec fn bishop_attack(a: int, b: int, c: int, d: int, e: int, f: int) -> bool {
        if c + d == e + f {
            !(a + b == c + d && Self::between(a, c, e))
        } else if c - d == e - f {
            !(a - b == c - d && Self::between(a, c, e))
        } else {
            false
        }
    }

    pub open spec fn can_capture_one(a: int, b: int, c: int, d: int, e: int, f: int) -> bool {
        Self::rook_attack(a, b, c, d, e, f) || Self::bishop_attack(a, b, c, d, e, f)
    }

    pub fn min_moves_to_capture_the_queen(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32) -> (result: i32)
        requires
            1 <= a <= 8,
            1 <= b <= 8,
            1 <= c <= 8,
            1 <= d <= 8,
            1 <= e <= 8,
            1 <= f <= 8,
            a != c || b != d,
            a != e || b != f,
            c != e || d != f,
        ensures
            result as int == if Self::can_capture_one(a as int, b as int, c as int, d as int, e as int, f as int) { 1int } else { 2int },
    {
    }
}

}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_end_from(x: int, cur: int, rem: int, pos: int) -> int
        decreases 63 - pos, rem,
    {
        if pos >= 63 || rem <= 0 {
            cur
        } else {
            let bit64 = 1i64 << (pos as i32);
            if ((x as i64) & bit64) != 0 {
                Self::min_end_from(x, cur, rem, pos + 1)
            } else {
                let cur2 = if ((rem as i64) & 1i64) == 1i64 { ((cur as i64) | bit64) as int } else { cur };
                Self::min_end_from(x, cur2, rem / 2, pos + 1)
            }
        }
    }

    pub open spec fn min_end_spec(n: int, x: int, result: int) -> bool {
        &&& 1 <= n <= 100_000_000
        &&& 1 <= x <= 100_000_000
        &&& result <= 9_223_372_036_854_775_807
        &&& result == Self::min_end_from(x, x, n - 1, 0)
    }

    pub fn min_end(n: i32, x: i32) -> (result: i64)
        requires
            1 <= n <= 100_000_000,
            1 <= x <= 100_000_000,
        ensures
            Self::min_end_spec(n as int, x as int, result as int),
    {
    }
}

}

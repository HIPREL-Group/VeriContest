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

    #[verifier::exec_allows_no_decreases_clause]
    pub fn min_end(n: i32, x: i32) -> (result: i64)
        requires
            1 <= n <= 100_000_000,
            1 <= x <= 100_000_000,
        ensures
            Self::min_end_spec(n as int, x as int, result as int),
    {
        let mut result = x as i64;
        let mut remaining = (n - 1) as i64;
        let mut pos = 0i32;
        let xx = x as i64;

        while pos < 63 && remaining > 0
            invariant
                1 <= n <= 100_000_000,
                1 <= x <= 100_000_000,
                0 <= pos <= 63,
                0 <= remaining,
                xx == x as i64,
                result <= 9_223_372_036_854_775_807i64,
                Self::min_end_from(x as int, result as int, remaining as int, pos as int)
                    == Self::min_end_from(x as int, x as int, n as int - 1, 0),
        {
            assert(0 <= pos < 63);
            let position = 1i64 << pos;
            if (xx & position) == 0 {
                let old_result = result;
                let old_remaining = remaining;
                let old_pos = pos;
                assert(((x as i64) & position) == 0);
                if (remaining & 1) == 1 {
                    result = result | position;
                }
                assert(Self::min_end_from(x as int, old_result as int, old_remaining as int, old_pos as int)
                    == Self::min_end_from(x as int, result as int, remaining / 2, pos as int + 1));
                remaining = remaining / 2;
            } else {
                assert(((x as i64) & position) != 0);
                assert(Self::min_end_from(x as int, result as int, remaining as int, pos as int)
                    == Self::min_end_from(x as int, result as int, remaining as int, pos as int + 1));
            }
            pos = pos + 1;
        }
        assert(!(pos < 63 && remaining > 0));
        assert(pos >= 63 || remaining <= 0);
        assert(Self::min_end_from(x as int, result as int, remaining as int, pos as int) == result as int);
        result
    }
}

}

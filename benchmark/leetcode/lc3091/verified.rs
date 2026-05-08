use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn imin(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn ops_for_m(k: int, m: int) -> int {
        if k <= 0 || m <= 0 {
            0
        } else {
            (m - 1) + (k - 1) / m
        }
    }

    pub open spec fn min_ops_upto(k: int, upto: int) -> int
        decreases upto,
    {
        if upto <= 1 {
            Self::ops_for_m(k, 1)
        } else {
            Self::imin(Self::min_ops_upto(k, upto - 1), Self::ops_for_m(k, upto))
        }
    }

    pub open spec fn min_operations_spec(k: int) -> int {
        if k <= 0 {
            0
        } else {
            Self::min_ops_upto(k, k)
        }
    }

    pub fn min_operations(k: i32) -> (result: i32)
        requires
            1 <= k <= 100000,
        ensures
            result as int == Self::min_operations_spec(k as int),
    {
        let mut best: i32 = k - 1;
        let mut m: i32 = 2;

        proof {
            assert(Self::min_ops_upto(k as int, 1) == Self::ops_for_m(k as int, 1));
            assert(best as int == Self::min_ops_upto(k as int, 1));
        }

        while m <= k
            invariant
                1 <= k <= 100000,
                2 <= m <= k + 1,
                best as int == Self::min_ops_upto(k as int, m as int - 1),
            decreases (k - m + 1) as int,
        {
            let ops: i32 = (m - 1) + (k - 1) / m;
            let ghost old_best = best as int;

            if ops < best {
                best = ops;
            }

            proof {
                assert(m as int >= 2);
                assert(ops as int == Self::ops_for_m(k as int, m as int));
                if ops < old_best as i32 {
                    assert(best as int == ops as int);
                } else {
                    assert(best as int == old_best);
                }
                assert(best as int == Self::imin(old_best, ops as int));
                assert(Self::min_ops_upto(k as int, m as int)
                    == Self::imin(Self::min_ops_upto(k as int, m as int - 1), Self::ops_for_m(k as int, m as int)));
                assert(old_best == Self::min_ops_upto(k as int, m as int - 1));
                assert(best as int == Self::min_ops_upto(k as int, m as int));
            }

            m = m + 1;
        }

        proof {
            assert(m == k + 1);
            assert(best as int == Self::min_ops_upto(k as int, k as int));
            assert(Self::min_operations_spec(k as int) == Self::min_ops_upto(k as int, k as int));
        }

        best
    }
}

}

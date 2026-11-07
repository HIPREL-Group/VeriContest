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
    }
}

}

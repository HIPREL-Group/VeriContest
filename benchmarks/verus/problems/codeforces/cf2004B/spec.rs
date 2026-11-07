use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_int(a: int, b: int) -> int {
        if a >= b {
            a
        } else {
            b
        }
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b {
            a
        } else {
            b
        }
    }

    pub open spec fn intersection_len(l: int, r: int, L: int, R: int) -> int {
        Self::min_int(r, R) - Self::max_int(l, L) + 1
    }

    pub open spec fn min_doors_answer(l: int, r: int, L: int, R: int) -> int {
        let inter = Self::intersection_len(l, r, L, R);
        if inter <= 0 {
            1
        } else {
            (inter - 1)
                + (if l != L {
                    1int
                } else {
                    0int
                })
                + (if r != R {
                    1int
                } else {
                    0int
                })
        }
    }

    pub fn min_doors_to_lock(l: i32, r: i32, L: i32, R: i32) -> (result: i32)
        requires
            1 <= l < r <= 100,
            1 <= L < R <= 100,
        ensures
            result as int == Self::min_doors_answer(l as int, r as int, L as int, R as int),
            1 <= result <= 99,
    {
    }
}

}

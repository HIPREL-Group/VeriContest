use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn delta_step(base: i64, other: i64) -> int {
        if other < base {
            -1
        } else if other > base {
            1
        } else {
            0
        }
    }

    pub open spec fn shift_delta(a: Seq<i64>, l: int, r: int) -> int
        recommends
            0 <= l <= r < a.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::shift_delta(a, l, r - 1) + Self::delta_step(a[l], a[r])
        }
    }

    pub fn best_shift(a: Vec<i64>) -> (result: (usize, usize))
        requires
            1 <= a.len() <= 2000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 2000,
        ensures
            0 <= result.0 <= result.1 < a.len(),
            forall|l: int, r: int| 0 <= l <= r < a.len() ==> Self::shift_delta(a@, result.0 as int, result.1 as int) <= #[trigger] Self::shift_delta(a@, l, r),
    {
    }
}

}

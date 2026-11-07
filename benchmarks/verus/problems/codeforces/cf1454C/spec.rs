use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_x_segments(a: Seq<i64>, x: int, end: int) -> nat
        recommends
            0 <= end <= a.len(),
        decreases end,
    {
        if end <= 0 {
            0nat
        } else if a[end - 1] as int == x {
            if end >= 2 && a[end - 2] as int == x {
                Self::count_x_segments(a, x, end - 1)
            } else {
                Self::count_x_segments(a, x, end - 1) + 1
            }
        } else {
            Self::count_x_segments(a, x, end - 1)
        }
    }

    pub open spec fn min_ops_for_value(a: Seq<i64>, x: int) -> nat {
        let segs = Self::count_x_segments(a, x, a.len() as int);
        if segs == 0 {
            (a.len() + 1) as nat
        } else {
            let left = if a[0] as int == x { 1int } else { 0int };
            let right = if a[a.len() - 1] as int == x { 1int } else { 0int };
            (segs as int + 1 - left - right) as nat
        }
    }

    pub open spec fn min_ops_upto(a: Seq<i64>, x_end: int) -> nat
        decreases x_end,
    {
        if x_end <= 0 {
            (a.len() + 1) as nat
        } else {
            let prev = Self::min_ops_upto(a, x_end - 1);
            let cur = Self::min_ops_for_value(a, x_end);
            if cur < prev { cur } else { prev }
        }
    }

    pub open spec fn min_operations(a: Seq<i64>) -> nat {
        Self::min_ops_upto(a, a.len() as int)
    }

    pub fn min_ops(a: Vec<i64>) -> (result: u64)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= a.len(),
        ensures
            result as int == Self::min_operations(a@),
    {
    }
}

}

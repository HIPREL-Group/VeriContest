use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn remaining_val(a: Seq<i64>, i: int) -> int
        recommends
            0 <= i < a.len(),
        decreases i,
    {
        if i <= 0 {
            a[0] as int
        } else {
            let prev = Self::remaining_val(a, i - 1);
            if prev <= a[i] as int {
                a[i] as int - prev
            } else {
                0int
            }
        }
    }

    pub open spec fn is_sortable(a: Seq<i64>) -> bool {
        forall |i: int| 0 <= i < a.len() as int - 1 ==> Self::remaining_val(a, i) <= #[trigger] a[i + 1] as int
    }

    pub fn can_sort(a: Vec<i64>) -> (result: bool)
        requires
            2 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
        ensures
            result == Self::is_sortable(a@),
    {
    }
}

}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_d_for_index(i: int) -> int {
        i + 2
    }

    pub open spec fn good_at(a: Seq<i64>, i: int) -> bool
        recommends
            0 <= i < a.len(),
    {
        exists|d: int| 2 <= d <= Self::max_d_for_index(i) && #[trigger] ((a[i] as int) % d) != 0
    }

    pub open spec fn can_erase_spec(a: Seq<i64>) -> bool {
        forall|i: int| 0 <= i < a.len() ==> Self::good_at(a, i)
    }

    pub fn can_erase_all(a: Vec<i64>) -> (ok: bool)
        requires
            1 <= a.len() <= 100_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            ok == Self::can_erase_spec(a@),
    {
    }
}

}

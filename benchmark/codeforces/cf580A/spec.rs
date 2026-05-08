use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_nd_contiguous(seq: Seq<i64>, l: int, r: int) -> bool {
    &&& 0 <= l <= r < seq.len()
    &&& forall|k: int| l <= k < r ==> #[trigger] seq[k] <= seq[k + 1]
}

impl Solution {
    pub fn longest_non_decreasing_run(a: Vec<i64>) -> (result: usize)
        requires
            1 <= a.len() <= 100_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            1 <= result as int <= a.len() as int,
            exists|l: int, r: int|
                0 <= l <= r < a.len() as int && is_nd_contiguous(a@, l, r) && r - l + 1 == result as int,
            forall|l: int, r: int|
                0 <= l <= r < a.len() as int && is_nd_contiguous(a@, l, r)
                    ==> r - l + 1 <= result as int,
    {
    }
}

}

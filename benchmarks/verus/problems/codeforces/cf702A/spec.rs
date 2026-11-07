use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_strict_inc_contiguous(seq: Seq<i64>, l: int, r: int) -> bool {
    &&& 0 <= l <= r < seq.len()
    &&& forall|k: int| l <= k < r ==> #[trigger] seq[k] < seq[k + 1]
}

impl Solution {
    pub fn max_increasing_subarray_len(n: usize, a: Vec<i64>) -> (res: usize)
        requires
            1 <= n <= 100_000,
            n == a.len(),
            forall|t: int| 0 <= t < a.len() ==> 1 <= #[trigger] a[t] <= 1_000_000_000,
        ensures
            1 <= res as int && res as int <= n as int,
            exists|l: int, r: int|
                0 <= l <= r < n as int && is_strict_inc_contiguous(a@, l, r)
                    && r - l + 1 == res as int,
            forall|l: int, r: int|
                0 <= l <= r < n as int && is_strict_inc_contiguous(a@, l, r)
                    ==> r - l + 1 <= res as int,
    {
    }
}

}

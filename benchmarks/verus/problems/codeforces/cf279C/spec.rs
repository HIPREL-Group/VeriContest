use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn non_decreasing(seq: Seq<i64>, lo: int, hi: int) -> bool
    recommends lo <= hi,
{
    forall|i: int| lo <= i && i < hi ==> #[trigger] seq[i] <= seq[i + 1]
}

pub open spec fn non_increasing(seq: Seq<i64>, lo: int, hi: int) -> bool
    recommends lo <= hi,
{
    forall|i: int| lo <= i && i < hi ==> #[trigger] seq[i] >= seq[i + 1]
}

pub open spec fn is_ladder(seq: Seq<i64>, l: int, r: int) -> bool
    recommends 0 <= l && l <= r && r < seq.len(),
{
    exists|k: int|
        l <= k && k <= r && non_decreasing(seq, l, k) && non_increasing(seq, k, r)
}

impl Solution {
    pub fn query_ladders(arr: Vec<i64>, queries: Vec<(i32, i32)>) -> (res: Vec<bool>)
        requires
            1 <= arr.len() <= 100_000,
            1 <= queries.len() <= 100_000,
            forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
            forall|q: int|
                0 <= q < queries.len() ==> {
                    let (l1, r1) = #[trigger] queries[q];
                    1 <= l1 && l1 <= r1 && (r1 as int) <= arr.len()
                },
        ensures
            res.len() == queries.len(),
            forall|k: int|
                0 <= k && k < res.len() ==> (#[trigger] res[k] == is_ladder(arr@, (queries[k].0 as int) - 1, (queries[k].1 as int) - 1)),
    {
    }
}

}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_fold(s: Seq<i32>) -> i32
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::xor_fold(s.drop_last()) ^ s.last()
        }
    }

    pub open spec fn range_xor(arr: Seq<i32>, l: int, r: int) -> i32
        recommends
            0 <= l <= r < arr.len(),
    {
        Self::xor_fold(arr.subrange(l, r + 1))
    }

    pub fn xor_queries(arr: Vec<i32>, queries: Vec<Vec<i32>>) -> (answer: Vec<i32>)
        requires
            1 <= arr.len() <= 30_000,
            1 <= queries.len() <= 30_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
            forall |k: int|
                0 <= k < queries.len() ==> #[trigger] queries[k].len() == 2
                    && 0 <= queries[k][0] <= queries[k][1] < arr.len() as i32,
        ensures
            answer.len() == queries.len(),
            forall |k: int| 0 <= k < queries.len() ==> {
                let l = queries[k][0] as int;
                let r = queries[k][1] as int;
                #[trigger] answer[k] == Self::range_xor(arr@, l, r)
            },
    {
    }
}

}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn appears_in_row(nums: Seq<Seq<i32>>, row: int, v: int, end: int) -> bool {
        exists|r: int| 0 <= r < end && #[trigger] nums[row][r] == v
    }

    pub open spec fn in_all_arrays(nums: Seq<Seq<i32>>, v: int, end: int) -> bool {
        forall|q: int| 0 <= q < end ==> #[trigger] Self::appears_in_row(nums, q, v, nums[q].len() as int)
    }

    pub fn intersection(nums: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i].len() >= 1,
            forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums[i].len() ==> 1 <= #[trigger] nums[i][j] <= 1000,
        ensures
            forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
            forall|p: int| 0 <= p < result.len() ==> #[trigger] Self::in_all_arrays(nums.deep_view(), result[p] as int, nums.len() as int),
            forall|v: int| 1 <= v <= 1000 && #[trigger] Self::in_all_arrays(nums.deep_view(), v, nums.len() as int) ==>
                exists|p: int| 0 <= p < result.len() && result[p] as int == v,
    {
    }
}

}

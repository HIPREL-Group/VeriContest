use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn same_parity_adjacent(nums: Seq<i32>, i: int) -> bool
        recommends
            0 <= i + 1 < nums.len(),
    {
        nums[i] % 2 == nums[i + 1] % 2
    }

    pub open spec fn query_is_special(nums: Seq<i32>, query: Vec<i32>) -> bool
        recommends
            query@.len() == 2,
            0 <= query@[0] <= query@[1] < nums.len(),
    {
        forall |k: int| query@[0] <= k < query@[1] ==> !(#[trigger] Self::same_parity_adjacent(nums, k))
    }

    pub fn is_array_special(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> (answer: Vec<bool>)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            1 <= queries.len() <= 100_000,
            forall |i: int| 0 <= i < queries.len() ==>
                queries[i].len() == 2
                && 0 <= queries[i][0] <= queries[i][1] < nums.len(),
        ensures
            answer.len() == queries.len(),
            forall |i: int| 0 <= i < queries.len() ==> #[trigger] answer[i] == Self::query_is_special(nums@, queries[i]),
    {
    }
}

}
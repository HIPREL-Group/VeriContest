use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_x_prefix(nums: Seq<i32>, x: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_x_prefix(nums, x, end - 1)
                + if nums[end - 1] as int == x { 1int } else { 0int }
        }
    }

    pub open spec fn query_answer_ok(nums: Seq<i32>, x: int, k: int, value: int) -> bool {
        if value == -1 {
            Self::count_x_prefix(nums, x, nums.len() as int) < k
        } else {
            &&& 0 <= value < nums.len()
            &&& nums[value] as int == x
            &&& Self::count_x_prefix(nums, x, value) == k - 1
            &&& Self::count_x_prefix(nums, x, value + 1) == k
        }
    }

    pub open spec fn kth_occurrence_from(nums: Seq<i32>, x: int, k: int, idx: int, seen: int) -> int
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            -1
        } else {
            let hit = if nums[idx] as int == x { 1int } else { 0int };
            let seen2 = seen + hit;
            if nums[idx] as int == x && seen2 == k {
                idx
            } else {
                Self::kth_occurrence_from(nums, x, k, idx + 1, seen2)
            }
        }
    }

    pub open spec fn kth_occurrence_index(nums: Seq<i32>, x: int, k: int) -> int {
        if k <= 0 { -1 } else { Self::kth_occurrence_from(nums, x, k, 0, 0) }
    }

    pub fn occurrences_of_element(nums: Vec<i32>, queries: Vec<i32>, x: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100000,
            1 <= queries.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
            forall |i: int| 0 <= i < queries.len() ==> 1 <= #[trigger] queries[i] <= 100000,
            1 <= x <= 10000,
        ensures
            result.len() == queries.len(),
            forall |qi: int| 0 <= qi < queries.len()
                ==> Self::query_answer_ok(nums@, x as int, queries[qi] as int, #[trigger] result[qi] as int),
    {
    }
}

}

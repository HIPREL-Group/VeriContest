use vstd::prelude::*;

fn main() {}

verus! {
    pub struct Solution;

    impl Solution {
        pub open spec fn count_zeros(nums: Seq<i32>, end: int) -> int
            decreases end,
        {
            if end <= 0 {
                0
            } else {
                (if nums[end - 1] == 0 { 1int } else { 0int }) + Self::count_zeros(nums, end - 1)
            }
        }

        pub open spec fn count_ones(nums: Seq<i32>, start: int, end: int) -> int
            decreases end - start,
        {
            if start >= end {
                0
            } else {
                (if nums[start] == 1 { 1int } else { 0int }) + Self::count_ones(nums, start + 1, end)
            }
        }

        pub open spec fn div_score(nums: Seq<i32>, i: int) -> int {
            Self::count_zeros(nums, i) + Self::count_ones(nums, i, nums.len() as int)
        }

        pub fn max_score_indices(nums: Vec<i32>) -> (res: Vec<i32>)
            requires
                1 <= nums.len() <= 100000,
                forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0 || nums[i] == 1,
            ensures
                res.len() >= 1,
                forall|j: int| 0 <= j < res.len() ==> 0 <= #[trigger] res[j] <= nums@.len() as i32,
                forall|j: int| 0 <= j < res.len() ==> Self::div_score(nums@, (#[trigger] res[j]) as int) == Self::div_score(nums@, res[0] as int),
                forall|k: int| 0 <= k <= nums@.len() as int ==> Self::div_score(nums@, res[0] as int) >= #[trigger] Self::div_score(nums@, k),
                forall|k: int| 0 <= k <= nums@.len() as int && #[trigger] Self::div_score(nums@, k) == Self::div_score(nums@, res[0] as int) ==> exists|j: int| 0 <= j < res.len() && #[trigger] res[j] == k as i32,
                forall|j1: int, j2: int| 0 <= j1 < res.len() && 0 <= j2 < res.len() && j1 != j2 ==> #[trigger] res[j1] != #[trigger] res[j2],
        {
        }
    }
}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_ge_k(nums: Seq<i32>, k: int) -> bool {
        forall |i: int| 0 <= i < nums.len() ==> nums[i] as int >= k
    }

    pub open spec fn count_lt_prefix(nums: Seq<i32>, k: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_lt_prefix(nums, k, end - 1)
                + if (nums[end - 1] as int) < k { 1int } else { 0int }
        }
    }

    pub open spec fn count_lt_k(nums: Seq<i32>, k: int) -> int {
        Self::count_lt_prefix(nums, k, nums.len() as int)
    }

    pub open spec fn min_operations_spec(nums: Seq<i32>, k: int, res: int) -> bool {
        &&& 2 <= nums.len() <= 200_000
        &&& 1 <= k <= 1_000_000_000
        &&& forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000
        &&& 0 <= res < nums.len()
        &&& (Self::all_ge_k(nums, k) <==> res == 0)
        &&& (Self::count_lt_k(nums, k) == 1 ==> res == 1)
        &&& res <= Self::count_lt_k(nums, k)
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            2 <= nums.len() <= 200_000,
            1 <= k <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            Self::min_operations_spec(nums@, k as int, res as int),
    {
    }
}

}

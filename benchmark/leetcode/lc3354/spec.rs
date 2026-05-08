use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_prefix(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i <= nums.len(),
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::sum_prefix(nums, i - 1) + nums[i - 1] as int
        }
    }

    pub open spec fn contribution(nums: Seq<i32>, total: int, i: int) -> int
        recommends
            0 <= i < nums.len(),
    {
        if nums[i] != 0 {
            0
        } else {
            let d = total - 2 * Self::sum_prefix(nums, i);
            if d == 0 {
                2
            } else if d == 1 || d == -1 {
                1
            } else {
                0
            }
        }
    }

    pub open spec fn count_prefix(nums: Seq<i32>, total: int, i: int) -> int
        recommends
            0 <= i <= nums.len(),
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::count_prefix(nums, total, i - 1) + Self::contribution(nums, total, i - 1)
        }
    }

    pub open spec fn count_valid_spec(nums: Seq<i32>) -> int
        recommends nums.len() > 0
    {
        let total = Self::sum_prefix(nums, nums.len() as int);
        Self::count_prefix(nums, total, nums.len() as int)
    }

    pub fn count_valid_selections(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 0,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] <= 100,
            exists|i: int| 0 <= i < nums.len() && nums[i] == 0,
        ensures
            result as int == Self::count_valid_spec(nums@),
    {
    }
}

}

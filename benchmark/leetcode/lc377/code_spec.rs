use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contribution(nums: Seq<i32>, target: nat, idx: nat) -> int
        decreases target, idx,
    {
        if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
            Self::combination_count(nums, ((target as int) - nums[idx as int] as int) as nat)
        } else {
            0
        }
    }

    pub open spec fn prefix_count(nums: Seq<i32>, target: nat, end: nat) -> int
        decreases target, end,
    {
        if end == 0 {
            0
        } else {
            Self::prefix_count(nums, target, (end - 1) as nat)
                + Self::contribution(nums, target, (end - 1) as nat)
        }
    }

    pub open spec fn combination_count(nums: Seq<i32>, target: nat) -> int
        decreases target,
    {
        if target == 0 {
            1
        } else {
            Self::prefix_count(nums, target, nums.len() as nat)
        }
    }

    fn combo_rec(nums: &Vec<i32>, t: usize) -> (res: i32)
        requires
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            nums.len() <= 200,
            Self::combination_count(nums@, t as nat) <= i32::MAX,
        ensures
            res as int == Self::combination_count(nums@, t as nat),
        decreases t,
    {
        if t == 0 {
            return 1;
        }
        let mut total: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len() {
            let num = nums[j];
            if (num as usize) <= t {
                let sub = Self::combo_rec(nums, t - num as usize);
                total = total + sub;
            }
            j += 1;
        }
        total
    }

    pub fn combination_sum4(nums: Vec<i32>, target: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
            1 <= target <= 1000,
            Self::combination_count(nums@, target as nat) <= i32::MAX,
        ensures
            res as int == Self::combination_count(nums@, target as nat),
    {
        Self::combo_rec(&nums, target as usize)
    }
}

}

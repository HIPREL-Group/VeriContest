use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn fits(v: i32, target: i32) -> bool {
        (v | target) == target
    }

    pub open spec fn min_ops_from(nums: Seq<i32>, target: i32, i: int, cur: i32) -> int
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            0
        } else {
            let cur2 = cur & nums[i];
            if Self::fits(cur2, target) {
                let a = Self::min_ops_from(nums, target, i + 1, 1_073_741_823i32);
                let b = 1 + Self::min_ops_from(nums, target, i + 1, cur2);
                if a < b { a } else { b }
            } else {
                1 + Self::min_ops_from(nums, target, i + 1, cur2)
            }
        }
    }

    pub open spec fn achievable(nums: Seq<i32>, k: int, target: i32) -> bool {
        Self::min_ops_from(nums, target, 0, 1_073_741_823i32) <= k
    }

    pub fn min_or_after_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            0 <= k < nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1_073_741_824,
        ensures
            Self::achievable(nums@, k as int, result),
            forall |v: i32| 0 <= v < 1_073_741_824i32 && Self::achievable(nums@, k as int, v)
                ==> result as int <= v as int,
    {
    }
}

}

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains(nums: Seq<i32>, value: i32) -> bool {
        exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] == value
    }

    pub open spec fn sequential_prefix_len(nums: Seq<i32>) -> nat
        decreases nums.len(),
    {
        if nums.len() == 0 {
            0nat
        } else if nums.len() == 1 {
            1nat
        } else if nums[1] == nums[0] + 1 {
            1nat + Self::sequential_prefix_len(nums.subrange(1, nums.len() as int))
        } else {
            1nat
        }
    }

    pub open spec fn prefix_sum(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0int
        } else {
            Self::prefix_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    pub open spec fn sequential_prefix_sum(nums: Seq<i32>) -> int {
        Self::prefix_sum(nums, Self::sequential_prefix_len(nums) as int)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn missing_integer(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            res >= Self::sequential_prefix_sum(nums@),
            !Self::contains(nums@, res),
            forall |x: int| Self::sequential_prefix_sum(nums@) <= x < res ==> #[trigger] Self::contains(nums@, x as i32),
            1 <= res,
    {
        let n = nums.len();

        let mut prefix_sum = nums[0];
        let mut i: usize = 1;
        
        while i < n && nums[i] == nums[i - 1] + 1
        {
            prefix_sum += nums[i];
            i += 1;
        }

        let mut candidate = prefix_sum;
        let mut found = false;
        while !found
        {
            let mut exists = false;
            let mut j: usize = 0;
            while j < n && !exists
            {
                if nums[j] == candidate {
                    exists = true;
                }
                j += 1;
            }

            if !exists {
                found = true;
            } else {
                candidate += 1;
            }
        }

        candidate
    }
}

}

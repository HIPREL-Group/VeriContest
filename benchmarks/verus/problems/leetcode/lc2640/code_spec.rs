use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_prefix(nums: Seq<i32>, upto: int) -> int
        recommends
            1 <= upto <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        decreases upto,
    {
        if upto <= 1 {
            nums[0] as int
        } else {
            let prev = Self::max_prefix(nums, upto - 1);
            if prev >= nums[upto - 1] as int { prev } else { nums[upto - 1] as int }
        }
    }

    pub open spec fn conv_at(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000000000,
    {
        nums[i] as int + Self::max_prefix(nums, i + 1)
    }

    pub open spec fn score_upto(nums: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000000000,
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::score_upto(nums, upto - 1) + Self::conv_at(nums, upto - 1)
        }
    }

    pub fn find_prefix_score(nums: Vec<i32>) -> (result: Vec<i64>)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() ==>
                #[trigger] result[i] as int == Self::score_upto(nums@, i + 1),
    {
        let n = nums.len();
        let mut ans: Vec<i64> = Vec::new();
        let mut mx: i32 = nums[0];
        let mut sum: i64 = nums[0] as i64 + mx as i64;
        ans.push(sum);

        let mut i: usize = 1;
        while i < n {
            if nums[i] > mx {
                mx = nums[i];
            }
            sum = sum + nums[i] as i64 + mx as i64;
            ans.push(sum);
            i = i + 1;
        }

        ans
    }
}

}

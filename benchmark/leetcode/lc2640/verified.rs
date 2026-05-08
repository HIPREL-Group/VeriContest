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
        proof {
            assert(mx as int == Self::max_prefix(nums@, 1));
            assert(Self::conv_at(nums@, 0) == nums[0] as int + Self::max_prefix(nums@, 1));
            assert(Self::score_upto(nums@, 1) == Self::score_upto(nums@, 0) + Self::conv_at(nums@, 0));
            assert(sum as int == Self::score_upto(nums@, 1));
            assert(ans[0] as int == Self::score_upto(nums@, 1));
            assert(0 <= sum as int <= 2000000000);
        }

        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100000,
                1 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000000000,
                mx as int == Self::max_prefix(nums@, i as int),
                1 <= mx <= 1000000000,
                sum as int == Self::score_upto(nums@, i as int),
                ans.len() == i,
                forall |k: int| 0 <= k < ans.len() ==> #[trigger] ans[k] as int == Self::score_upto(nums@, k + 1),
                0 <= sum as int <= i as int * 2000000000,
            decreases n - i,
        {
            let old_i = i;
            let old_sum = sum;
            if nums[i] > mx {
                mx = nums[i];
            }
            sum = sum + nums[i] as i64 + mx as i64;
            ans.push(sum);
            proof {
                assert(Self::max_prefix(nums@, (i + 1) as int)
                    == if Self::max_prefix(nums@, i as int) >= nums[i as int] as int {
                        Self::max_prefix(nums@, i as int)
                    } else {
                        nums[i as int] as int
                    });
                assert(Self::conv_at(nums@, i as int) == nums[i as int] as int + Self::max_prefix(nums@, (i + 1) as int));
                assert(Self::score_upto(nums@, (i + 1) as int)
                    == Self::score_upto(nums@, i as int) + Self::conv_at(nums@, i as int));
                assert(old_sum as int == Self::score_upto(nums@, old_i as int));
                assert(1 <= nums@[old_i as int] <= 1000000000);
                assert(1 <= mx <= 1000000000);
                assert(0 <= nums@[old_i as int] as int + mx as int <= 2000000000);
                assert(sum as int == old_sum as int + (nums@[old_i as int] as int + mx as int));
                assert(0 <= sum as int);
                assert(sum as int <= (old_i as int + 1) * 2000000000);
                assert(ans[old_i as int] as int == Self::score_upto(nums@, old_i as int + 1));
            }
            i = i + 1;
        }

        ans
    }
}

}

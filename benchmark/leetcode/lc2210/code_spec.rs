use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn next_diff_or_len(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums.len(),
        decreases nums.len() - i,
    {
        if i + 1 >= nums.len() {
            nums.len() as int
        } else if nums[i + 1] != nums[i] {
            i + 1
        } else {
            Self::next_diff_or_len(nums, i + 1)
        }
    }

    pub open spec fn is_hv_start(nums: Seq<i32>, i: int) -> bool {
        if 1 <= i < nums.len() - 1 && nums[i] != nums[i - 1] {
            let r = Self::next_diff_or_len(nums, i);
            r < nums.len()
                && ((nums[i] > nums[i - 1] && nums[i] > nums[r])
                    || (nums[i] < nums[i - 1] && nums[i] < nums[r]))
        } else {
            false
        }
    }

    pub open spec fn count_hv_upto(nums: Seq<i32>, k: int) -> int
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 1 {
            0
        } else {
            Self::count_hv_upto(nums, k - 1) + if Self::is_hv_start(nums, k - 1) { 1int } else { 0int }
        }
    }

    pub fn count_hill_valley(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::count_hv_upto(nums@, nums.len() as int - 1),
            0 <= result <= nums.len(),
    {
        let n = nums.len();
        let mut i: usize = 1;
        let mut count: i32 = 0;

        while i + 1 < n {
            if nums[i] == nums[i - 1] {
                i = i + 1;
                continue;
            }

            let mut r = i + 1;
            while r < n && nums[r] == nums[i] {
                r = r + 1;
            }

            if r < n {
                if (nums[i] > nums[i - 1] && nums[i] > nums[r])
                    || (nums[i] < nums[i - 1] && nums[i] < nums[r])
                {
                    count = count + 1;
                }
            }

            i = i + 1;
        }

        count
    }
}

}

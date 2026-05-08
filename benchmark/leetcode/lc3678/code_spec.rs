use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains(nums: Seq<i32>, value: int) -> bool {
        exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] as int == value
    }

    pub open spec fn seq_sum(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn smallest_absent(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            1 <= res,
            (res as int) * nums.len() as int > Self::seq_sum(nums@, nums.len() as int),
            !Self::contains(nums@, res as int),
            forall |x: int| 1 <= x < res as int
                && x * nums.len() as int > Self::seq_sum(nums@, nums.len() as int)
                ==> Self::contains(nums@, x),
    {
        let n_usize = nums.len();
        let n = n_usize as i32;

        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n_usize {
            sum += nums[i];
            i += 1;
        }

        let mut candidate: i32 = 1;
        let mut candidate_times_n: i32 = n;
        while candidate < 101 {
            let mut exists = false;
            let mut j: usize = 0;
            while j < n_usize && !exists {
                if nums[j] == candidate {
                    exists = true;
                }
                j += 1;
            }

            if candidate_times_n > sum && !exists {
                return candidate;
            }
            candidate += 1;
            candidate_times_n += n;
        }

        101
    }
}

}

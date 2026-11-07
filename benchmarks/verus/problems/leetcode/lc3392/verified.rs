use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_count_subarrays(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if 2 * (nums[k - 1] as int + nums[k + 1] as int) == nums[k] as int {
        spec_count_subarrays(nums, k - 1) + 1
    } else {
        spec_count_subarrays(nums, k - 1)
    }
}

proof fn lemma_count_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k,
        k + 2 <= nums.len(),
    ensures
        0 <= spec_count_subarrays(nums, k) <= k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_count_bounds(nums, k - 1);
    }
}

impl Solution {
    pub fn count_subarrays(nums: Vec<i32>) -> (count: i32)
        requires
            3 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            count == spec_count_subarrays(nums@, (nums.len() - 2) as int),
    {
        let n = nums.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i + 2 < n
            invariant
                n == nums.len(),
                3 <= n <= 100,
                forall |j: int| 0 <= j < nums.len() ==> -100 <= #[trigger] nums[j] <= 100,
                0 <= i <= n - 2,
                count as int == spec_count_subarrays(nums@, i as int),
                0 <= count <= i as i32,
            decreases n - i,
        {
            proof {
                lemma_count_bounds(nums@, (i + 1) as int);
            }
            if 2 * (nums[i] + nums[i + 2]) == nums[i + 1] {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

} 

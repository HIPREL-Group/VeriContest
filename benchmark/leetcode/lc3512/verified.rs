use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_sum(nums, k - 1) + nums[k - 1] as int
    }
}

proof fn lemma_sum_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures
        k <= spec_sum(nums, k) <= 1000 * k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_sum_bounds(nums, k - 1);
        assert(1000 * (k - 1) + 1000 == 1000 * k) by(nonlinear_arith);
    }
}

impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            1 <= k <= 100,
        ensures
            result == spec_sum(nums@, nums.len() as int) % (k as int),
    {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 1000,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000,
                0 <= i <= n,
                total as int == spec_sum(nums@, i as int),
                i as i32 <= total <= 1000 * i as i32,
            decreases n - i,
        {
            proof {
                lemma_sum_bounds(nums@, (i + 1) as int);
            }
            total += nums[i];
            i += 1;
        }
        assert(total as int == spec_sum(nums@, n as int));
        assert(total >= 1);
        assert((total as u32) as int == total as int);
        assert((k as u32) as int == k as int);
        ((total as u32) % (k as u32)) as i32
    }
}

} 

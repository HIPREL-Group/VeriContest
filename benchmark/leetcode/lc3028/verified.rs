use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_sum(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_prefix_sum(nums, k - 1) + nums[k - 1] as int
    }
}

pub open spec fn spec_boundary_count(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if spec_prefix_sum(nums, k) == 0 {
        spec_boundary_count(nums, k - 1) + 1
    } else {
        spec_boundary_count(nums, k - 1)
    }
}

proof fn lemma_prefix_sum_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10,
    ensures
        -10 * k <= spec_prefix_sum(nums, k) <= 10 * k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_prefix_sum_bounds(nums, k - 1);
        assert(-10 * (k - 1) - 10 == -10 * k) by(nonlinear_arith);
        assert(10 * (k - 1) + 10 == 10 * k) by(nonlinear_arith);
    }
}

proof fn lemma_boundary_count_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10,
    ensures
        0 <= spec_boundary_count(nums, k) <= k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_boundary_count_bounds(nums, k - 1);
    }
}

impl Solution {
    pub fn return_to_boundary_count(nums: Vec<i32>) -> (count: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10,
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != 0,
        ensures
            count == spec_boundary_count(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut position: i32 = 0;
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100,
                forall |j: int| 0 <= j < nums.len() ==> -10 <= #[trigger] nums[j] <= 10,
                0 <= i <= n,
                position as int == spec_prefix_sum(nums@, i as int),
                -1000 <= position <= 1000,
                count as int == spec_boundary_count(nums@, i as int),
                0 <= count <= i as i32,
            decreases n - i,
        {
            proof {
                lemma_prefix_sum_bounds(nums@, (i + 1) as int);
                lemma_boundary_count_bounds(nums@, (i + 1) as int);
            }
            position += nums[i];
            if position == 0 {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

} 

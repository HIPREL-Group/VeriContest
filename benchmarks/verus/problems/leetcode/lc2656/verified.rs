use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_max(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 1 {
        nums[0] as int
    } else if nums[i - 1] > spec_max(nums, i - 1) {
        nums[i - 1] as int
    } else {
        spec_max(nums, i - 1)
    }
}

pub open spec fn spec_max_sum(m: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_max_sum(m, k - 1) + m + (k - 1)
    }
}

proof fn lemma_spec_max_bounds(nums: Seq<i32>, i: int)
    requires
        1 <= i <= nums.len(),
        forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
    ensures
        1 <= spec_max(nums, i) <= 100,
    decreases i,
{
    if i <= 1 {
    } else {
        lemma_spec_max_bounds(nums, i - 1);
    }
}

proof fn lemma_spec_max_sum_bounds(m: int, k: int)
    requires
        1 <= m <= 100,
        0 <= k <= 100,
    ensures
        0 <= spec_max_sum(m, k) <= k * (m + k),
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_spec_max_sum_bounds(m, k - 1);
        assert(spec_max_sum(m, k) == spec_max_sum(m, k - 1) + m + (k - 1));
        assert((k - 1) * (m + k - 1) + m + (k - 1) <= k * (m + k)) by(nonlinear_arith)
            requires 1 <= m, 1 <= k;
    }
}

impl Solution {
    pub fn maximize_sum(nums: Vec<i32>, k: i32) -> (score: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            score == spec_max_sum(spec_max(nums@, nums.len() as int), k as int),
    {
        let n = nums.len();
        let mut max_val: i32 = nums[0];
        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
                1 <= i <= n,
                max_val as int == spec_max(nums@, i as int),
                1 <= max_val <= 100,
            decreases n - i,
        {
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        let mut score: i32 = 0;
        let mut j: i32 = 0;
        while j < k
            invariant
                1 <= max_val <= 100,
                1 <= k <= 100,
                0 <= j <= k,
                score as int == spec_max_sum(max_val as int, j as int),
                0 <= score <= 20000,
            decreases k - j,
        {
            proof {
                lemma_spec_max_sum_bounds(max_val as int, (j + 1) as int);
                assert((j + 1) * (max_val as int + (j + 1)) <= 100 * 200) by(nonlinear_arith)
                    requires 0 <= j <= 99, 1 <= max_val <= 100i32;
            }
            score += max_val + j;
            j += 1;
        }
        score
    }
}

} 

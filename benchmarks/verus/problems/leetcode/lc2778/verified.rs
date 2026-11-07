use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum_of_squares(nums: Seq<i32>, n: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if n % k == 0 {
        spec_sum_of_squares(nums, n, k - 1) + (nums[k - 1] as int) * (nums[k - 1] as int)
    } else {
        spec_sum_of_squares(nums, n, k - 1)
    }
}

proof fn lemma_sum_of_squares_bounds(nums: Seq<i32>, n: int, k: int)
    requires
        0 <= k <= n,
        n == nums.len(),
        1 <= n <= 50,
        forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 50,
    ensures
        0 <= spec_sum_of_squares(nums, n, k) <= 2500 * k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_sum_of_squares_bounds(nums, n, k - 1);
        assert(0 <= spec_sum_of_squares(nums, n, k - 1) <= 2500 * (k - 1));
        if n % k == 0 {
            assert(1 <= nums[k - 1] <= 50);
            assert(nums[k - 1] as int * (nums[k - 1] as int) <= 2500) by(nonlinear_arith)
                requires 1 <= nums[k - 1] <= 50;
            assert(2500 * (k - 1) + 2500 == 2500 * k) by(nonlinear_arith);
        }
    }
}

impl Solution {
    pub fn sum_of_squares(nums: Vec<i32>) -> (total: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            total == spec_sum_of_squares(nums@, nums.len() as int, nums.len() as int),
    {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 50,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 50,
                0 <= i <= n,
                total as int == spec_sum_of_squares(nums@, n as int, i as int),
                0 <= total <= 2500 * i as i32,
            decreases n - i,
        {
            proof {
                lemma_sum_of_squares_bounds(nums@, n as int, (i + 1) as int);
            }
            if n % (i + 1) == 0 {
                total += nums[i] * nums[i];
            }
            i += 1;
        }
        total
    }
}

} 

use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::prefix_sum(nums, k - 1) + nums[k - 1] as int
        }
    }

    proof fn prefix_sum_bounds(nums: Seq<i32>, k: int)
        requires
            0 <= k <= nums.len(),
            forall|j: int| 0 <= j < nums.len() ==> -100 <= #[trigger] nums[j] <= 100,
        ensures
            -100 * k <= Self::prefix_sum(nums, k) <= 100 * k,
        decreases k
    {
        if k > 0 {
            Self::prefix_sum_bounds(nums, k - 1);
            assert(Self::prefix_sum(nums, k) == Self::prefix_sum(nums, k - 1) + nums[k - 1] as int);
        }
    }

    pub fn min_start_value(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            result >= 1,
            exists|k: int| 0 <= k <= nums.len() && result == 1 - Self::prefix_sum(nums@, k),
            forall|k: int| 0 <= k <= nums.len() ==> 1 - Self::prefix_sum(nums@, k) <= result,
    {
        let n = nums.len();
        let mut min_sum: i32 = 0;
        let mut sum: i32 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < n ==> -100 <= #[trigger] nums[j] <= 100,
                sum as int == Self::prefix_sum(nums@, i as int),
                -10000 <= sum <= 10000,
                -10000 <= min_sum <= 0,
                exists|k: int| 0 <= k <= i && min_sum as int == Self::prefix_sum(nums@, k),
                forall|k: int| 0 <= k <= i ==> #[trigger] Self::prefix_sum(nums@, k) >= min_sum as int,
            decreases n - i,
        {
            proof {
                assert(Self::prefix_sum(nums@, i as int + 1) == Self::prefix_sum(nums@, i as int) + nums@[i as int] as int);
                Self::prefix_sum_bounds(nums@, i as int + 1);
                assert(-10000 <= Self::prefix_sum(nums@, i as int + 1) <= 10000) by (nonlinear_arith)
                    requires
                        -100 * (i as int + 1) <= Self::prefix_sum(nums@, i as int + 1),
                        Self::prefix_sum(nums@, i as int + 1) <= 100 * (i as int + 1),
                        i < n,
                        n <= 100;
            }
            sum = sum + nums[i];
            proof {
                assert(sum as int == Self::prefix_sum(nums@, i as int + 1));
                let new_min = if sum < min_sum { sum } else { min_sum };
                assert forall|k: int| 0 <= k <= i as int + 1 implies Self::prefix_sum(nums@, k) >= new_min as int by {
                    if k <= i as int {
                        assert(Self::prefix_sum(nums@, k) >= min_sum as int);
                    }
                };
            }
            if sum < min_sum {
                min_sum = sum;
            }
            i += 1;
        }
        1 - min_sum
    }
}

}

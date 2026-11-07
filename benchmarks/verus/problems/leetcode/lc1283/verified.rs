use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_div(x: int, d: int) -> int {
        (x + d - 1) / d
    }

    pub open spec fn sum_prefix(nums: Seq<i32>, d: int, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::sum_prefix(nums, d, n - 1) + Self::ceil_div(nums[n - 1] as int, d)
        }
    }

    pub open spec fn sum_by_divisor(nums: Seq<i32>, d: int) -> int {
        Self::sum_prefix(nums, d, nums.len() as int)
    }

    proof fn lemma_sum_prefix_upper_bound(nums: Seq<i32>, d: int, n: int)
        requires
            1 <= d,
            0 <= n <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            Self::sum_prefix(nums, d, n) <= n * 1_000_000,
        decreases n
    {
        if n > 0 {
            Self::lemma_sum_prefix_upper_bound(nums, d, n - 1);
            assert(Self::ceil_div(nums[n - 1] as int, d) <= nums[n - 1] as int) by (nonlinear_arith)
                requires
                    1 <= d,
                    nums[n - 1] >= 1,
            {
            }
        }
    }

    proof fn lemma_ceil_div_monotonic(x: int, d1: int, d2: int)
        requires
            1 <= x,
            1 <= d1 <= d2,
        ensures
            Self::ceil_div(x, d2) <= Self::ceil_div(x, d1),
    {
        assert((x + d2 - 1) * d1 <= (x + d1 - 1) * d2) by (nonlinear_arith)
            requires
                1 <= x,
                1 <= d1 <= d2,
        {
        }
        assert((x + d2 - 1) / d2 <= (x + d1 - 1) / d1) by (nonlinear_arith)
            requires
                1 <= d1,
                1 <= d2,
                (x + d2 - 1) * d1 <= (x + d1 - 1) * d2,
        {
        }
    }

    proof fn lemma_sum_prefix_monotonic(nums: Seq<i32>, d1: int, d2: int, n: int)
        requires
            0 <= n <= nums.len(),
            1 <= d1 <= d2,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            Self::sum_prefix(nums, d2, n) <= Self::sum_prefix(nums, d1, n),
        decreases n
    {
        if n > 0 {
            Self::lemma_sum_prefix_monotonic(nums, d1, d2, n - 1);
            Self::lemma_ceil_div_monotonic(nums[n - 1] as int, d1, d2);
        }
    }

    proof fn lemma_sum_prefix_at_max(nums: Seq<i32>, n: int, k: int)
        requires
            0 <= n <= nums.len(),
            k >= 1,
            forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] as int <= k,
        ensures
            Self::sum_prefix(nums, k, n) == n,
        decreases n
    {
        if n > 0 {
            Self::lemma_sum_prefix_at_max(nums, n - 1, k);
            assert(Self::ceil_div(nums[n - 1] as int, k) == 1) by (nonlinear_arith)
                requires 1 <= nums[n - 1] as int <= k, k >= 1
            {
            }
        }
    }

    proof fn lemma_sum_by_divisor_monotonic(nums: Seq<i32>, d1: int, d2: int)
        requires
            1 <= d1 <= d2,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            Self::sum_by_divisor(nums, d2) <= Self::sum_by_divisor(nums, d1),
    {
        Self::lemma_sum_prefix_monotonic(nums, d1, d2, nums.len() as int);
    }

    fn sum_with_divisor(nums: &Vec<i32>, divisor: i32) -> (sum: i64)
        requires
            1 <= nums.len() <= 50_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
            1 <= divisor <= 1_000_000,
        ensures
            sum as int == Self::sum_by_divisor(nums@, divisor as int),
            0 <= sum <= 50_000 * 1_000_000,
    {
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                1 <= nums.len() <= 50_000,
                sum as int == Self::sum_prefix(nums@, divisor as int, i as int),
                0 <= sum as int <= i as int * 1_000_000,
                1 <= divisor <= 1_000_000,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000,
            decreases nums.len() - i
        {
            let n = nums[i];
            let term: i64 = (n as i64 + divisor as i64 - 1) / divisor as i64;
            proof {
                assert(term as int == Self::ceil_div(nums[i as int] as int, divisor as int)) by (nonlinear_arith)
                    requires
                        1 <= nums[i as int] as int <= 1_000_000,
                        1 <= divisor as int <= 1_000_000,
                        n as int == nums[i as int] as int,
                        term as int == (n as int + divisor as int - 1) / divisor as int {}
                assert(1 <= term as int <= 1_000_000) by (nonlinear_arith)
                    requires
                        1 <= nums[i as int] as int <= 1_000_000,
                        1 <= divisor as int,
                        term as int == (nums[i as int] as int + divisor as int - 1) / divisor as int {}
                assert(sum as int + term as int <= (i as int + 1) * 1_000_000) by (nonlinear_arith)
                    requires
                        0 <= sum as int <= i as int * 1_000_000,
                        1 <= term as int <= 1_000_000 {}
                assert((i as int + 1) * 1_000_000 <= 50_000 * 1_000_000) by (nonlinear_arith)
                    requires i < 50_000 {}
                assert(50_000 * 1_000_000 < 9_223_372_036_854_775_807);
            }
            sum += term;
            i += 1;
        }
        sum
    }

    pub fn smallest_divisor(nums: Vec<i32>, threshold: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 50_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
            nums.len() <= threshold <= 1_000_000,
        ensures
            1 <= res <= 1_000_000,
            Self::sum_by_divisor(nums@, res as int) <= threshold as int,
            forall |d: int| 1 <= d < res ==> #[trigger] Self::sum_by_divisor(nums@, d) > threshold as int,
    {
        proof {
            Self::lemma_sum_prefix_at_max(nums@, nums.len() as int, 1_000_000);
            assert(Self::sum_by_divisor(nums@, 1_000_000) == nums.len() as int);
        }

        let mut left: i32 = 1;
        let mut right: i32 = 1_000_000;

        while left < right
            invariant
                1 <= left <= right <= 1_000_000,
                1 <= nums.len() <= 50_000,
                Self::sum_by_divisor(nums@, right as int) <= threshold as int,
                forall |d: int| 1 <= d < left ==> #[trigger] Self::sum_by_divisor(nums@, d) > threshold as int,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
                nums.len() <= threshold <= 1_000_000,
            decreases right - left
        {
            let mid = left + (right - left) / 2;
            let sum = Self::sum_with_divisor(&nums, mid);
            if sum <= threshold as i64 {
                right = mid;
            } else {
                proof {
                    assert(Self::sum_by_divisor(nums@, mid as int) > threshold as int) by (nonlinear_arith)
                        requires
                            sum as int == Self::sum_by_divisor(nums@, mid as int),
                            sum > threshold as i64,
                    {
                    }
                    assert forall |d: int| 1 <= d < mid + 1 implies Self::sum_by_divisor(nums@, d) > threshold as int by {
                        if d < left {
                        } else {
                            assert(left <= d <= mid);
                            Self::lemma_sum_by_divisor_monotonic(nums@, d, mid as int);
                            assert(Self::sum_by_divisor(nums@, d) >= Self::sum_by_divisor(nums@, mid as int));
                        }
                    }
                }
                left = mid + 1;
            }
        }

        left
    }
}

}

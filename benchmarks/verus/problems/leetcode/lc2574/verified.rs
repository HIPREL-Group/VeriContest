use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum(nums: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        spec_sum(nums, lo, hi - 1) + nums[hi - 1] as int
    }
}

pub open spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

proof fn lemma_spec_sum_bounds(nums: Seq<i32>, lo: int, hi: int, lb: int, ub: int)
    requires
        0 <= lo <= hi <= nums.len(),
        lb >= 0,
        ub >= 0,
        forall |k: int| lo <= k < hi ==> lb <= #[trigger] nums[k] as int <= ub,
    ensures
        lb * (hi - lo) <= spec_sum(nums, lo, hi) <= ub * (hi - lo),
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        lemma_spec_sum_bounds(nums, lo, hi - 1, lb, ub);
        assert(lb * (hi - lo) <= spec_sum(nums, lo, hi)) by (nonlinear_arith)
            requires
                lb * (hi - 1 - lo) <= spec_sum(nums, lo, hi - 1),
                lb <= nums[hi - 1] as int,
                spec_sum(nums, lo, hi) == spec_sum(nums, lo, hi - 1) + nums[hi - 1] as int,
        {}
        assert(spec_sum(nums, lo, hi) <= ub * (hi - lo)) by (nonlinear_arith)
            requires
                spec_sum(nums, lo, hi - 1) <= ub * (hi - 1 - lo),
                nums[hi - 1] as int <= ub,
                spec_sum(nums, lo, hi) == spec_sum(nums, lo, hi - 1) + nums[hi - 1] as int,
        {}
    }
}

proof fn lemma_spec_sum_split(nums: Seq<i32>, lo: int, mid: int, hi: int)
    requires
        lo <= mid <= hi <= nums.len(),
    ensures
        spec_sum(nums, lo, hi) == spec_sum(nums, lo, mid) + spec_sum(nums, mid, hi),
    decreases hi - mid,
{
    if mid >= hi {
    } else {
        lemma_spec_sum_split(nums, lo, mid, hi - 1);
    }
}

impl Solution {
    pub fn left_right_difference(nums: Vec<i32>) -> (answer: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            answer.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==>
                #[trigger] answer[i] == spec_abs(
                    spec_sum(nums@, 0, i) - spec_sum(nums@, i + 1, nums.len() as int)
                ),
    {
        let n = nums.len();
        let mut total_sum: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
                0 <= i <= n,
                total_sum as int == spec_sum(nums@, 0, i as int),
                0 <= total_sum <= 100_000 * i as i64,
            decreases n - i,
        {
            proof {
                lemma_spec_sum_bounds(nums@, 0, (i + 1) as int, 1, 100_000);
            }
            total_sum += nums[i] as i64;
            i += 1;
        }

        let mut answer: Vec<i32> = vec![0i32; n];
        let mut left_sum: i64 = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                n == nums.len(),
                1 <= n <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
                total_sum as int == spec_sum(nums@, 0, n as int),
                0 <= total_sum <= 100_000_000i64,
                0 <= j <= n,
                answer.len() == n,
                left_sum as int == spec_sum(nums@, 0, j as int),
                0 <= left_sum <= 100_000 * j as i64,
                forall |k: int| 0 <= k < j ==>
                    #[trigger] answer[k] == spec_abs(
                        spec_sum(nums@, 0, k) - spec_sum(nums@, k + 1, n as int)
                    ),
            decreases n - j,
        {
            let right_sum: i64 = total_sum - left_sum - nums[j] as i64;

            proof {
                lemma_spec_sum_split(nums@, 0, j as int, n as int);
                lemma_spec_sum_split(nums@, j as int, j + 1, n as int);
                
                assert(spec_sum(nums@, j as int, j as int) == 0);
                assert(spec_sum(nums@, j as int, (j + 1) as int) ==
                    spec_sum(nums@, j as int, j as int) + nums@[j as int] as int);
            }

            let diff: i64 = left_sum - right_sum;

            proof {
                lemma_spec_sum_bounds(nums@, j + 1, n as int, 0, 100_000);
            }

            if diff >= 0 {
                answer.set(j, diff as i32);
            } else {
                answer.set(j, (-diff) as i32);
            }

            proof {
                assert(answer[j as int] == spec_abs(
                    spec_sum(nums@, 0, j as int) - spec_sum(nums@, j + 1, n as int)
                ));
                lemma_spec_sum_bounds(nums@, 0, (j + 1) as int, 0, 100_000);
            }

            left_sum += nums[j] as i64;
            j += 1;
        }
        answer
    }
}

} 

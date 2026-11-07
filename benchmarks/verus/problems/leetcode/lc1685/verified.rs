use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn sum_abs_diffs(nums: Seq<i32>, i: int, j: int) -> int
    decreases nums.len() - j,
{
    if j >= nums.len() {
        0
    } else {
        spec_abs(nums[i] as int - nums[j] as int) + sum_abs_diffs(nums, i, j + 1)
    }
}

pub open spec fn spec_sum(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else {
        nums[start] as int + spec_sum(nums, start + 1, end)
    }
}

proof fn spec_sum_split(nums: Seq<i32>, lo: int, mid: int, hi: int)
    requires
        0 <= lo <= mid <= hi <= nums.len(),
    ensures
        spec_sum(nums, lo, hi) == spec_sum(nums, lo, mid) + spec_sum(nums, mid, hi),
    decreases mid - lo,
{
    if lo < mid {
        spec_sum_split(nums, lo + 1, mid, hi);
    }
}

proof fn spec_sum_upper_bound(nums: Seq<i32>, lo: int, hi: int, ub: int)
    requires
        0 <= lo <= hi <= nums.len(),
        forall |k: int| lo <= k < hi ==> #[trigger] nums[k] as int <= ub,
    ensures
        spec_sum(nums, lo, hi) <= (hi - lo) * ub,
    decreases hi - lo,
{
    if lo < hi {
        spec_sum_upper_bound(nums, lo + 1, hi, ub);
        assert(spec_sum(nums, lo, hi) == nums[lo] as int + spec_sum(nums, lo + 1, hi));
        assert(nums[lo] as int <= ub);
        assert(spec_sum(nums, lo + 1, hi) <= (hi - lo - 1) * ub);
        assert(spec_sum(nums, lo, hi) <= (hi - lo) * ub) by (nonlinear_arith)
            requires
                spec_sum(nums, lo, hi) == nums[lo] as int + spec_sum(nums, lo + 1, hi),
                nums[lo] as int <= ub,
                spec_sum(nums, lo + 1, hi) <= (hi - lo - 1) * ub;
    } else {
        assert(spec_sum(nums, lo, hi) == 0int);
        assert(hi - lo == 0int);
    }
}

proof fn spec_sum_lower_bound(nums: Seq<i32>, lo: int, hi: int, lb: int)
    requires
        0 <= lo <= hi <= nums.len(),
        forall |k: int| lo <= k < hi ==> #[trigger] nums[k] as int >= lb,
    ensures
        spec_sum(nums, lo, hi) >= (hi - lo) * lb,
    decreases hi - lo,
{
    if lo < hi {
        spec_sum_lower_bound(nums, lo + 1, hi, lb);
        assert(spec_sum(nums, lo, hi) == nums[lo] as int + spec_sum(nums, lo + 1, hi));
        assert(nums[lo] as int >= lb);
        assert(spec_sum(nums, lo + 1, hi) >= (hi - lo - 1) * lb);
        assert(spec_sum(nums, lo, hi) >= (hi - lo) * lb) by (nonlinear_arith)
            requires
                spec_sum(nums, lo, hi) == nums[lo] as int + spec_sum(nums, lo + 1, hi),
                nums[lo] as int >= lb,
                spec_sum(nums, lo + 1, hi) >= (hi - lo - 1) * lb;
    } else {
        assert(spec_sum(nums, lo, hi) == 0int);
        assert(hi - lo == 0int);
    }
}

proof fn sad_left(nums: Seq<i32>, idx: int, j: int)
    requires
        0 <= j <= idx < nums.len(),
        forall |k: int, l: int| 0 <= k <= l < nums.len() ==> #[trigger] nums[k] <= #[trigger] nums[l],
    ensures
        sum_abs_diffs(nums, idx, j) ==
            (idx - j) * (nums[idx] as int) - spec_sum(nums, j, idx) + sum_abs_diffs(nums, idx, idx),
    decreases idx - j,
{
    if j < idx {
        sad_left(nums, idx, j + 1);
        assert(nums[j] <= nums[idx]);
        assert(spec_abs(nums[idx] as int - nums[j] as int) == nums[idx] as int - nums[j] as int);
        assert(sum_abs_diffs(nums, idx, j) ==
            spec_abs(nums[idx] as int - nums[j] as int) + sum_abs_diffs(nums, idx, j + 1));
        assert(spec_sum(nums, j, idx) == nums[j] as int + spec_sum(nums, j + 1, idx));
        assert(sum_abs_diffs(nums, idx, j) ==
            (idx - j) * (nums[idx] as int) - spec_sum(nums, j, idx) + sum_abs_diffs(nums, idx, idx))
            by (nonlinear_arith)
            requires
                sum_abs_diffs(nums, idx, j) ==
                    (nums[idx] as int - nums[j] as int) + sum_abs_diffs(nums, idx, j + 1),
                sum_abs_diffs(nums, idx, j + 1) ==
                    (idx - j - 1) * (nums[idx] as int) - spec_sum(nums, j + 1, idx) + sum_abs_diffs(nums, idx, idx),
                spec_sum(nums, j, idx) == nums[j] as int + spec_sum(nums, j + 1, idx);
    } else {
        assert(j == idx);
        assert(idx - j == 0int);
        assert(spec_sum(nums, j, idx) == 0int);
        assert((idx - j) * (nums[idx] as int) == 0int);
    }
}

proof fn sad_right(nums: Seq<i32>, idx: int, j: int)
    requires
        0 <= idx,
        idx < j,
        j <= nums.len(),
        forall |k: int, l: int| 0 <= k <= l < nums.len() ==> #[trigger] nums[k] <= #[trigger] nums[l],
    ensures
        sum_abs_diffs(nums, idx, j) ==
            spec_sum(nums, j, nums.len() as int) - (nums.len() - j) * (nums[idx] as int),
    decreases nums.len() - j,
{
    if j < nums.len() {
        sad_right(nums, idx, j + 1);
        assert(nums[idx] <= nums[j]);
        assert(spec_abs(nums[idx] as int - nums[j] as int) == nums[j] as int - nums[idx] as int);
        assert(sum_abs_diffs(nums, idx, j) ==
            spec_abs(nums[idx] as int - nums[j] as int) + sum_abs_diffs(nums, idx, j + 1));
        assert(spec_sum(nums, j, nums.len() as int) ==
            nums[j] as int + spec_sum(nums, j + 1, nums.len() as int));
        assert(sum_abs_diffs(nums, idx, j) ==
            spec_sum(nums, j, nums.len() as int) - (nums.len() - j) * (nums[idx] as int))
            by (nonlinear_arith)
            requires
                sum_abs_diffs(nums, idx, j) ==
                    (nums[j] as int - nums[idx] as int) + sum_abs_diffs(nums, idx, j + 1),
                sum_abs_diffs(nums, idx, j + 1) ==
                    spec_sum(nums, j + 1, nums.len() as int) - (nums.len() - j - 1) * (nums[idx] as int),
                spec_sum(nums, j, nums.len() as int) ==
                    nums[j] as int + spec_sum(nums, j + 1, nums.len() as int);
    } else {
        assert(sum_abs_diffs(nums, idx, j) == 0int);
        assert(spec_sum(nums, j, nums.len() as int) == 0int);
        assert(nums.len() - j == 0int);
    }
}

proof fn sad_formula(nums: Seq<i32>, idx: int, n: int)
    requires
        n == nums.len(),
        0 <= idx < n,
        forall |k: int, l: int| 0 <= k <= l < n ==> #[trigger] nums[k] <= #[trigger] nums[l],
    ensures
        sum_abs_diffs(nums, idx, 0) ==
            (2 * idx - n) * (nums[idx] as int)
            + spec_sum(nums, 0, n) - 2 * spec_sum(nums, 0, idx),
{
    sad_left(nums, idx, 0);
    assert(spec_abs(nums[idx] as int - nums[idx] as int) == 0);
    assert(sum_abs_diffs(nums, idx, idx) ==
        spec_abs(nums[idx] as int - nums[idx] as int) + sum_abs_diffs(nums, idx, idx + 1));
    assert(sum_abs_diffs(nums, idx, idx) == sum_abs_diffs(nums, idx, idx + 1));
    sad_right(nums, idx, idx + 1);
    spec_sum_split(nums, 0, idx, n);
    spec_sum_split(nums, idx, idx + 1, n);
    assert(spec_sum(nums, idx, idx + 1) == nums[idx] as int + spec_sum(nums, idx + 1, idx + 1));
    assert(spec_sum(nums, idx + 1, idx + 1) == 0int);
    assert(sum_abs_diffs(nums, idx, 0) ==
        (2 * idx - n) * (nums[idx] as int)
        + spec_sum(nums, 0, n) - 2 * spec_sum(nums, 0, idx))
        by (nonlinear_arith)
        requires
            sum_abs_diffs(nums, idx, 0) ==
                idx * (nums[idx] as int) - spec_sum(nums, 0, idx)
                + sum_abs_diffs(nums, idx, idx + 1),
            sum_abs_diffs(nums, idx, idx + 1) ==
                spec_sum(nums, idx + 1, n) - (n - idx - 1) * (nums[idx] as int),
            spec_sum(nums, 0, n) == spec_sum(nums, 0, idx)
                + nums[idx] as int + spec_sum(nums, idx + 1, n);
}

proof fn sad_nonneg(nums: Seq<i32>, idx: int, j: int)
    requires
        0 <= idx < nums.len(),
        0 <= j,
    ensures
        sum_abs_diffs(nums, idx, j) >= 0,
    decreases nums.len() - j,
{
    if j < nums.len() {
        sad_nonneg(nums, idx, j + 1);
    } else {
        assert(sum_abs_diffs(nums, idx, j) == 0int);
    }
}

proof fn sad_upper_bound(nums: Seq<i32>, idx: int, j: int)
    requires
        0 <= idx < nums.len(),
        0 <= j <= nums.len(),
        forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
    ensures
        sum_abs_diffs(nums, idx, j) <= (nums.len() - j) * 9999,
    decreases nums.len() - j,
{
    if j < nums.len() {
        sad_upper_bound(nums, idx, j + 1);
        assert(1 <= nums[idx] <= 10_000);
        assert(1 <= nums[j] <= 10_000);
        assert(spec_abs(nums[idx] as int - nums[j] as int) <= 9999);
        assert(sum_abs_diffs(nums, idx, j) ==
            spec_abs(nums[idx] as int - nums[j] as int) + sum_abs_diffs(nums, idx, j + 1));
        assert(sum_abs_diffs(nums, idx, j) <= (nums.len() - j) * 9999) by (nonlinear_arith)
            requires
                sum_abs_diffs(nums, idx, j) ==
                    spec_abs(nums[idx] as int - nums[j] as int) + sum_abs_diffs(nums, idx, j + 1),
                spec_abs(nums[idx] as int - nums[j] as int) <= 9999,
                sum_abs_diffs(nums, idx, j + 1) <= (nums.len() - j - 1) * 9999;
    } else {
        assert(sum_abs_diffs(nums, idx, j) == 0int);
        assert(j == nums.len());
    }
}

impl Solution {
    pub fn get_sum_absolute_differences(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums@.len() <= 100_000,
            forall |i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < nums@.len() ==> nums@[i] <= nums@[j],
        ensures
            result@.len() == nums@.len(),
            forall |i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] as int == sum_abs_diffs(nums@, i, 0),
    {
        let n = nums.len() as i32;
        let mut total_sum: i32 = 0;
        let mut i: i32 = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                2 <= n <= 100_000,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] nums@[k] <= 10_000,
                total_sum as int == spec_sum(nums@, 0, i as int),
                0 <= total_sum <= i * 10_000,
            decreases n - i,
        {
            proof {
                assert(1 <= nums@[i as int] <= 10_000);
                spec_sum_split(nums@, 0, i as int, (i + 1) as int);
                assert(spec_sum(nums@, i as int, (i + 1) as int) ==
                    nums@[i as int] as int + spec_sum(nums@, (i + 1) as int, (i + 1) as int));
                assert(spec_sum(nums@, (i + 1) as int, (i + 1) as int) == 0int);
                spec_sum_upper_bound(nums@, 0, (i + 1) as int, 10_000);
                assert((i + 1) * 10_000 <= 1_000_000_000) by (nonlinear_arith)
                    requires i + 1 <= 100_000;
            }
            total_sum = total_sum + nums[i as usize];
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut prefix: i32 = 0;
        i = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                2 <= n <= 100_000,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] nums@[k] <= 10_000,
                forall |k: int, l: int| 0 <= k <= l < n ==> nums@[k] <= nums@[l],
                result@.len() == i as nat,
                prefix as int == spec_sum(nums@, 0, i as int),
                total_sum as int == spec_sum(nums@, 0, n as int),
                0 <= prefix <= i * 10_000,
                0 <= total_sum <= n * 10_000,
                forall |k: int| 0 <= k < i ==> #[trigger] result@[k] as int == sum_abs_diffs(nums@, k, 0),
            decreases n - i,
        {
            proof {
                sad_formula(nums@, i as int, n as int);
                sad_nonneg(nums@, i as int, 0);
                sad_upper_bound(nums@, i as int, 0);

                spec_sum_upper_bound(nums@, 0, i as int, nums@[i as int] as int);
                spec_sum_lower_bound(nums@, (i + 1) as int, n as int, nums@[i as int] as int);
                spec_sum_split(nums@, 0, i as int, n as int);
                spec_sum_split(nums@, i as int, (i + 1) as int, n as int);
                assert(spec_sum(nums@, i as int, (i + 1) as int) ==
                    nums@[i as int] as int + spec_sum(nums@, (i + 1) as int, (i + 1) as int));
                assert(spec_sum(nums@, (i + 1) as int, (i + 1) as int) == 0int);

                assert(0 <= i * (nums@[i as int] as int) <= 999_990_000) by (nonlinear_arith)
                    requires
                        0 <= i <= 99_999,
                        1 <= nums@[i as int] as int <= 10_000,
                {};

                assert(0 <= (n - 1 - i) * (nums@[i as int] as int) <= 999_990_000) by (nonlinear_arith)
                    requires
                        0 <= n - 1 - i <= 99_999,
                        1 <= nums@[i as int] as int <= 10_000,
                {};

                assert(sum_abs_diffs(nums@, i as int, 0) <= 100_000 * 9999);
            }

            let left = i * nums[i as usize] - prefix;
            let suffix = total_sum - prefix - nums[i as usize];
            let right = suffix - (n - 1 - i) * nums[i as usize];

            proof {
                assert((left + right) as int == sum_abs_diffs(nums@, i as int, 0)) by (nonlinear_arith)
                    requires
                        left as int == i as int * (nums@[i as int] as int) - prefix as int,
                        suffix as int == total_sum as int - prefix as int - nums@[i as int] as int,
                        right as int == suffix as int - (n as int - 1 - i as int) * (nums@[i as int] as int),
                        sum_abs_diffs(nums@, i as int, 0) ==
                            (2 * (i as int) - n as int) * (nums@[i as int] as int)
                            + total_sum as int - 2 * prefix as int;
            }

            result.push(left + right);

            proof {
                assert(result@[i as int] as int == sum_abs_diffs(nums@, i as int, 0));
            }

            proof {
                assert(1 <= nums@[i as int] <= 10_000);
                spec_sum_split(nums@, 0, i as int, (i + 1) as int);
                assert(spec_sum(nums@, i as int, (i + 1) as int) ==
                    nums@[i as int] as int + spec_sum(nums@, (i + 1) as int, (i + 1) as int));
                assert(spec_sum(nums@, (i + 1) as int, (i + 1) as int) == 0int);
                spec_sum_upper_bound(nums@, 0, (i + 1) as int, 10_000);
                assert((i + 1) * 10_000 <= 1_000_000_000) by (nonlinear_arith)
                    requires i + 1 <= 100_000;
            }
            prefix = prefix + nums[i as usize];
            i = i + 1;
        }

        result
    }
}

}

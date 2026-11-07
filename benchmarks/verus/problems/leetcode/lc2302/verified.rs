use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn subarray_sum(nums: Seq<i32>, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            nums[start] as int + Self::subarray_sum(nums, start + 1, end)
        }
    }

    pub open spec fn score(nums: Seq<i32>, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
    {
        Self::subarray_sum(nums, start, end) * (end - start)
    }

    pub open spec fn first_valid_start(nums: Seq<i32>, k: int, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
            1 <= k,
        decreases end - start,
    {
        if start >= end || Self::score(nums, start, end) < k {
            start
        } else {
            Self::first_valid_start(nums, k, start + 1, end)
        }
    }

    pub open spec fn end_count(nums: Seq<i32>, k: int, end: int) -> int
        recommends
            0 <= end <= nums.len(),
            1 <= k,
    {
        end - Self::first_valid_start(nums, k, 0, end)
    }

    pub open spec fn count_subarrays_prefix(nums: Seq<i32>, k: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
            1 <= k,
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_subarrays_prefix(nums, k, n - 1) + Self::end_count(nums, k, n)
        }
    }

    proof fn lemma_subarray_sum_bounds(nums: Seq<i32>, start: int, end: int)
        requires
            0 <= start <= end <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            0 <= Self::subarray_sum(nums, start, end),
            Self::subarray_sum(nums, start, end) <= (end - start) * 100_000,
        decreases end - start,
    {
        reveal_with_fuel(Solution::subarray_sum, 2);
        if start < end {
            Self::lemma_subarray_sum_bounds(nums, start + 1, end);
            assert(0 <= nums[start] as int <= 100_000);
            assert(Self::subarray_sum(nums, start, end)
                == nums[start] as int + Self::subarray_sum(nums, start + 1, end));
            assert(Self::subarray_sum(nums, start, end) <= (end - start) * 100_000) by (nonlinear_arith)
                requires
                    Self::subarray_sum(nums, start + 1, end) <= (end - (start + 1)) * 100_000,
                    nums[start] as int <= 100_000,
            {};
        }
    }

    proof fn lemma_subarray_sum_extend_right(nums: Seq<i32>, start: int, end: int)
        requires
            0 <= start <= end < nums.len(),
        ensures
            Self::subarray_sum(nums, start, end + 1)
                == Self::subarray_sum(nums, start, end) + nums[end] as int,
        decreases end - start,
    {
        reveal_with_fuel(Solution::subarray_sum, 2);
        if start < end {
            Self::lemma_subarray_sum_extend_right(nums, start + 1, end);
        }
    }

    proof fn lemma_score_extend_right(nums: Seq<i32>, start: int, end: int)
        requires
            0 <= start < end < nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            Self::score(nums, start, end) < Self::score(nums, start, end + 1),
        decreases end - start,
    {
        Self::lemma_subarray_sum_bounds(nums, start, end);
        Self::lemma_subarray_sum_extend_right(nums, start, end);
        assert(Self::subarray_sum(nums, start, end + 1)
            == Self::subarray_sum(nums, start, end) + nums[end] as int);
        assert(1 <= nums[end] as int);
        assert(Self::subarray_sum(nums, start, end + 1) > Self::subarray_sum(nums, start, end));
        assert(0 <= Self::subarray_sum(nums, start, end));
        assert(0 < end - start);
        assert(Self::score(nums, start, end)
            == Self::subarray_sum(nums, start, end) * (end - start));
        assert(Self::score(nums, start, end + 1)
            == Self::subarray_sum(nums, start, end + 1) * (end + 1 - start));
        assert(Self::score(nums, start, end) < Self::score(nums, start, end + 1)) by (nonlinear_arith)
            requires
                0 <= Self::subarray_sum(nums, start, end),
                Self::subarray_sum(nums, start, end) < Self::subarray_sum(nums, start, end + 1),
                0 < end - start,
                end - start < end + 1 - start,
        {};
    }

    proof fn lemma_score_shrink_left(nums: Seq<i32>, start: int, end: int)
        requires
            0 <= start < end <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            Self::score(nums, start + 1, end) < Self::score(nums, start, end),
        decreases end - start,
    {
        reveal_with_fuel(Solution::subarray_sum, 2);
        Self::lemma_subarray_sum_bounds(nums, start + 1, end);
        assert(Self::subarray_sum(nums, start, end)
            == nums[start] as int + Self::subarray_sum(nums, start + 1, end));
        assert(1 <= nums[start] as int);
        assert(Self::subarray_sum(nums, start + 1, end) < Self::subarray_sum(nums, start, end));
        assert(0 <= Self::subarray_sum(nums, start + 1, end));
        assert(0 <= end - (start + 1) < end - start);
        assert(Self::score(nums, start + 1, end)
            == Self::subarray_sum(nums, start + 1, end) * (end - (start + 1)));
        assert(Self::score(nums, start, end)
            == Self::subarray_sum(nums, start, end) * (end - start));
        if start + 1 == end {
            assert(Self::score(nums, start + 1, end) == 0);
            assert(Self::subarray_sum(nums, start, end) >= 1);
            assert(Self::score(nums, start, end) >= 1) by (nonlinear_arith)
                requires
                    Self::subarray_sum(nums, start, end) >= 1,
                    end - start >= 1,
            {};
        } else {
            assert(Self::score(nums, start + 1, end) < Self::score(nums, start, end)) by (nonlinear_arith)
                requires
                    0 <= Self::subarray_sum(nums, start + 1, end),
                    Self::subarray_sum(nums, start + 1, end) < Self::subarray_sum(nums, start, end),
                    0 <= end - (start + 1),
                    end - (start + 1) < end - start,
            {};
        }
    }

    proof fn lemma_invalid_mono_left(nums: Seq<i32>, k: int, start: int, pivot: int, end: int)
        requires
            0 <= start <= pivot < end <= nums.len(),
            1 <= k,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            Self::score(nums, pivot, end) >= k,
        ensures
            Self::score(nums, start, end) >= k,
        decreases pivot - start,
    {
        if start == pivot {
        } else {
            Self::lemma_invalid_mono_left(nums, k, start + 1, pivot, end);
            Self::lemma_score_shrink_left(nums, start, end);
            assert(Self::score(nums, start + 1, end) < Self::score(nums, start, end));
            assert(Self::score(nums, start + 1, end) >= k);
            assert(Self::score(nums, start, end) > Self::score(nums, start + 1, end));
            assert(Self::score(nums, start, end) >= k);
        }
    }

    proof fn lemma_first_valid_from_invalid_prefix(nums: Seq<i32>, k: int, start: int, left: int, end: int)
        requires
            0 <= start <= left <= end <= nums.len(),
            1 <= k,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            forall|s: int| start <= s < left ==> Self::score(nums, s, end) >= k,
            Self::score(nums, left, end) < k,
        ensures
            Self::first_valid_start(nums, k, start, end) == left,
        decreases left - start,
    {
        reveal_with_fuel(Solution::first_valid_start, 2);
        if start < left {
            assert(Self::score(nums, start, end) >= k);
            Self::lemma_first_valid_from_invalid_prefix(nums, k, start + 1, left, end);
        }
    }

    pub fn count_subarrays(nums: Vec<i32>, k: i64) -> (result: i64)
        requires
            1 <= nums.len() <= 100_000,
            1 <= k <= 1_000_000_000_000_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result >= 0,
            result as int == Self::count_subarrays_prefix(nums@, k as int, nums.len() as int),
    {
        let n = nums.len();
        let mut left = 0usize;
        let mut sum = 0i64;
        let mut answer = 0i64;
        let mut right = 0usize;

        while right < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                1 <= k <= 1_000_000_000_000_000,
                forall|i: int| 0 <= i < n ==> 1 <= #[trigger] nums@[i] <= 100_000,
                0 <= left <= right <= n,
                sum as int == Self::subarray_sum(nums@, left as int, right as int),
                0 <= sum as int,
                sum as int <= (right as int - left as int) * 100_000,
                Self::score(nums@, left as int, right as int) < k as int,
                left == 0 || Self::score(nums@, left as int - 1, right as int) >= k as int,
                answer >= 0,
                answer as int == Self::count_subarrays_prefix(nums@, k as int, right as int),
                answer as int <= right as int * (right as int + 1) / 2,
            decreases n - right,
        {
            proof {
                assert((right as int - left as int) * 100_000 <= 10_000_000_000) by (nonlinear_arith)
                    requires
                        0 <= right as int - left as int,
                        right as int <= 100_000,
                {};
                assert(sum as int + nums@[right as int] as int <= 10_000_100_000) by (nonlinear_arith)
                    requires
                        sum as int <= (right as int - left as int) * 100_000,
                        (right as int - left as int) * 100_000 <= 10_000_000_000,
                        nums@[right as int] as int <= 100_000,
                {};
                assert(10_000_100_000 < 9_223_372_036_854_775_807);
            }
            sum += nums[right] as i64;

            proof {
                Self::lemma_subarray_sum_extend_right(nums@, left as int, right as int);
                assert(sum as int == Self::subarray_sum(nums@, left as int, right as int + 1));
                Self::lemma_subarray_sum_bounds(nums@, left as int, right as int + 1);
                if left > 0 {
                    if left as int - 1 < right as int {
                        Self::lemma_score_extend_right(nums@, left as int - 1, right as int);
                        assert(Self::score(nums@, left as int - 1, right as int)
                            < Self::score(nums@, left as int - 1, right as int + 1));
                        assert(Self::score(nums@, left as int - 1, right as int) >= k as int);
                        assert(Self::score(nums@, left as int - 1, right as int + 1) >= k as int);
                    } else {
                        assert(left == right);
                        assert(Self::score(nums@, left as int - 1, right as int)
                            == nums@[left as int - 1] as int);
                        assert(Self::score(nums@, left as int - 1, right as int + 1)
                            == (nums@[left as int - 1] as int + nums@[right as int] as int) * 2);
                        assert(Self::score(nums@, left as int - 1, right as int + 1)
                            >= Self::score(nums@, left as int - 1, right as int));
                        assert(Self::score(nums@, left as int - 1, right as int + 1) >= k as int);
                    }
                }
            }

            proof {
                assert(sum as int * ((right as int + 1) - left as int)
                    <= 1_000_000_000_000_000) by (nonlinear_arith)
                    requires
                        0 <= sum as int,
                        sum as int <= ((right as int + 1) - left as int) * 100_000,
                        0 <= (right as int + 1) - left as int,
                        (right as int + 1) - left as int <= 100_000,
                {};
            }

            while left <= right && sum * (right - left + 1) as i64 >= k
                invariant
                    n == nums.len(),
                    1 <= n <= 100_000,
                    1 <= k <= 1_000_000_000_000_000,
                    forall|i: int| 0 <= i < n ==> 1 <= #[trigger] nums@[i] <= 100_000,
                    right < n,
                    0 <= left <= right + 1,
                    sum as int == Self::subarray_sum(nums@, left as int, right as int + 1),
                    0 <= sum as int,
                    sum as int <= ((right as int + 1) - left as int) * 100_000,
                    sum as int * ((right as int + 1) - left as int) <= 1_000_000_000_000_000,
                    left == 0 || Self::score(nums@, left as int - 1, right as int + 1) >= k as int,
                    answer >= 0,
                    answer as int == Self::count_subarrays_prefix(nums@, k as int, right as int),
                    answer as int <= right as int * (right as int + 1) / 2,
                decreases right + 1 - left,
            {
                proof {
                    reveal_with_fuel(Solution::subarray_sum, 2);
                    Self::lemma_subarray_sum_bounds(nums@, left as int + 1, right as int + 1);
                    assert(sum as int
                        == nums@[left as int] as int + Self::subarray_sum(nums@, left as int + 1, right as int + 1));
                    assert(sum as int >= nums@[left as int] as int);
                    
                    assert(sum as int * ((right as int + 1) - left as int) >= k as int);
                }
                let ghost old_left = left;
                let ghost old_sum = sum as int;
                let ghost old_product = old_sum * ((right as int + 1) - old_left as int);
                sum -= nums[left] as i64;
                left += 1;
                proof {
                    assert(old_sum == Self::subarray_sum(nums@, old_left as int, right as int + 1));
                    assert(sum as int == Self::subarray_sum(nums@, left as int, right as int + 1));
                    Self::lemma_subarray_sum_bounds(nums@, left as int, right as int + 1);
                    assert(old_product >= k as int);
                    assert(Self::score(nums@, old_left as int, right as int + 1) >= k as int);
                    assert(left as int - 1 == old_left as int);
                    assert(Self::score(nums@, left as int - 1, right as int + 1) >= k as int);
                    
                    assert(sum as int * ((right as int + 1) - left as int) <= old_product) by (nonlinear_arith)
                        requires
                            0 <= sum as int,
                            sum as int <= old_sum,
                            0 <= (right as int + 1) - left as int,
                            (right as int + 1) - left as int <= (right as int + 1) - old_left as int,
                            old_product == old_sum * ((right as int + 1) - old_left as int),
                    {};
                }
            }

            proof {
                if left <= right {
                    assert(sum as int * ((right as int + 1) - left as int) < k as int);
                    assert(Self::score(nums@, left as int, right as int + 1)
                        == sum as int * ((right as int + 1) - left as int));
                    assert(Self::score(nums@, left as int, right as int + 1) < k as int);
                } else {
                    assert(left == right + 1);
                    assert(sum as int == Self::subarray_sum(nums@, left as int, right as int + 1));
                    assert(Self::score(nums@, left as int, right as int + 1) == 0);
                    assert(0 < k as int);
                    assert(Self::score(nums@, left as int, right as int + 1) < k as int);
                }

                assert forall|s: int| 0 <= s < left as int implies #[trigger] Self::score(nums@, s, right as int + 1) >= k as int by {
                    if left > 0 {
                        Self::lemma_invalid_mono_left(nums@, k as int, s, left as int - 1, right as int + 1);
                    }
                };

                Self::lemma_first_valid_from_invalid_prefix(
                    nums@,
                    k as int,
                    0,
                    left as int,
                    right as int + 1,
                );
                assert(Self::first_valid_start(nums@, k as int, 0, right as int + 1) == left as int);
                reveal(Solution::end_count);
                assert(Self::end_count(nums@, k as int, right as int + 1)
                    == (right as int + 1) - left as int);
                reveal_with_fuel(Solution::count_subarrays_prefix, 2);
                assert(Self::count_subarrays_prefix(nums@, k as int, right as int + 1)
                    == Self::count_subarrays_prefix(nums@, k as int, right as int)
                        + Self::end_count(nums@, k as int, right as int + 1));
                assert(answer as int + ((right as int + 1) - left as int)
                    == Self::count_subarrays_prefix(nums@, k as int, right as int + 1));

                assert((right as int + 1) - left as int <= right as int + 1) by (nonlinear_arith) {};
                assert(answer as int + ((right as int + 1) - left as int)
                    <= (right as int + 1) * (right as int + 2) / 2) by (nonlinear_arith)
                    requires
                        answer as int <= right as int * (right as int + 1) / 2,
                        (right as int + 1) - left as int <= right as int + 1,
                {};
                assert((right as int + 1) * (right as int + 2) / 2 <= 5_000_050_000) by (nonlinear_arith)
                    requires
                        0 <= right as int,
                        right as int + 1 <= 100_000,
                {};
                assert(answer as int + ((right as int + 1) - left as int) <= 9_223_372_036_854_775_807int) by (nonlinear_arith)
                    requires
                        answer as int + ((right as int + 1) - left as int) <= 5_000_050_000,
                {};
            }

            answer += (right + 1 - left) as i64;
            right += 1;
        }

        answer
    }
}

}

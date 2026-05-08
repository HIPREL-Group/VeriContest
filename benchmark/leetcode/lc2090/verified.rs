use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_sum(nums: Seq<i32>, start: int, len: int) -> int
        recommends
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            Self::window_sum(nums, start, len - 1) + nums[start + len - 1] as int
        }
    }

    proof fn lemma_window_sum_step(nums: Seq<i32>, start: int, len: int)
        requires
            0 <= start,
            0 <= len,
            start + len < nums.len(),
        ensures
            Self::window_sum(nums, start, len + 1) == Self::window_sum(nums, start, len) + nums[start + len] as int,
    {
    }

    proof fn lemma_window_slide(nums: Seq<i32>, start: int, len: int)
        requires
            0 <= start,
            0 < len,
            start + len < nums.len(),
        ensures
            Self::window_sum(nums, start + 1, len)
                == Self::window_sum(nums, start, len) + nums[start + len] as int - nums[start] as int,
        decreases len,
    {
        reveal_with_fuel(Solution::window_sum, 2);
        if len > 1 {
            Self::lemma_window_slide(nums, start, len - 1);
        }
    }

    proof fn lemma_window_sum_nonneg(nums: Seq<i32>, start: int, len: int)
        requires
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
        ensures
            0 <= Self::window_sum(nums, start, len),
        decreases len,
    {
        if len > 0 {
            Self::lemma_window_sum_nonneg(nums, start, len - 1);
        }
    }

    proof fn lemma_window_sum_upper(nums: Seq<i32>, start: int, len: int)
        requires
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] <= 100_000,
        ensures
            Self::window_sum(nums, start, len) <= len * 100_000,
        decreases len,
    {
        if len > 0 {
            Self::lemma_window_sum_upper(nums, start, len - 1);
        }
    }

    pub fn get_averages(nums: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            0 <= k <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() ==> (
                if i < k as int || i + k as int >= (nums.len() as int) {
                    #[trigger] result[i] == -1
                } else {
                    #[trigger] result[i] as int == Self::window_sum(nums@, i - k as int, 2 * k as int + 1) / (2 * k as int + 1)
                }
            ),
    {
        let n = nums.len();
        let radius = k as usize;
        let window_len = 2 * radius + 1;
        let ghost k_int = k as int;
        let ghost n_int = n as int;
        let ghost radius_int = radius as int;
        let ghost window_len_int = window_len as int;
        let mut result: Vec<i32> = Vec::new();

        proof {
            assert(radius_int == k_int);
            assert(window_len_int == 2 * radius_int + 1);
            assert(window_len_int == 2 * k_int + 1);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                0 <= k <= 100_000,
                0 <= i <= n,
                result.len() == i,
                k_int == k as int,
                n_int == n as int,
                radius_int == radius as int,
                radius_int == k_int,
                window_len_int == window_len as int,
                window_len_int == 2 * radius_int + 1,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 100_000,
                forall |j: int| 0 <= j < result.len() ==> #[trigger] result@[j] == -1,
            decreases n - i,
        {
            let ghost old_result = result@;
            result.push(-1);
            proof {
                assert(result@ == old_result.push(-1i32));
                assert forall |j: int| 0 <= j < result.len() implies #[trigger] result@[j] == -1 by {
                    if j < old_result.len() {
                        assert(result@[j] == old_result[j]);
                    } else {
                        assert(j == old_result.len());
                    }
                }
            }
            i += 1;
        }

        if window_len > n {
            proof {
                assert(window_len_int > n_int);
                assert forall |j: int| 0 <= j < result.len() implies (
                    if j < k_int || j + k_int >= n_int {
                        #[trigger] result@[j] == -1
                    } else {
                        #[trigger] result@[j] as int == Self::window_sum(nums@, j - k_int, 2 * k_int + 1) / (2 * k_int + 1)
                    }
                ) by {
                    assert(result@[j] == -1);
                    if !(j < k_int || j + k_int >= n_int) {
                        assert(j >= k_int);
                        assert(j + k_int < n_int);
                        assert(j + k_int + 1 <= n_int) by (nonlinear_arith)
                            requires
                                j + k_int < n_int,
                        {};
                        assert(2 * k_int + 1 <= n_int) by (nonlinear_arith)
                            requires
                                0 <= k_int,
                                k_int <= j,
                                j + k_int + 1 <= n_int,
                        {};
                        assert(window_len_int <= n_int);
                        assert(false);
                    }
                }
            }
            return result;
        } else {
            let mut sum: i64 = 0;
            i = 0;
            while i < window_len
                invariant
                    n == nums.len(),
                    1 <= n <= 100_000,
                    0 <= k <= 100_000,
                    radius == k as usize,
                    window_len == 2 * radius + 1,
                    k_int == k as int,
                    n_int == n as int,
                    radius_int == radius as int,
                    radius_int == k_int,
                    window_len_int == window_len as int,
                    window_len_int == 2 * radius_int + 1,
                    window_len <= n,
                    0 <= i <= window_len,
                    forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 100_000,
                    result.len() == n,
                    forall |j: int| 0 <= j < result.len() ==> #[trigger] result@[j] == -1,
                    sum as int == Self::window_sum(nums@, 0, i as int),
                    0 <= sum as int <= (i as int) * 100_000,
                decreases window_len - i,
            {
                proof {
                    Self::lemma_window_sum_step(nums@, 0, i as int);
                    assert(sum as int + nums[i as int] as int <= ((i as int) + 1) * 100_000) by (nonlinear_arith)
                        requires
                            0 <= sum as int,
                            sum as int <= (i as int) * 100_000,
                            nums[i as int] as int <= 100_000,
                    {};
                }
                sum += nums[i] as i64;
                i += 1;
            }

            let denom = window_len as i64;
            let limit = n - radius;
            let mut center = radius;
            proof {
                assert(radius < limit) by (nonlinear_arith)
                    requires
                        window_len <= n,
                        window_len == 2 * radius + 1,
                        limit == n - radius,
                {};
            }
            while center < limit
                invariant
                    n == nums.len(),
                    1 <= n <= 100_000,
                    0 <= k <= 100_000,
                    radius == k as usize,
                    window_len == 2 * radius + 1,
                    k_int == k as int,
                    n_int == n as int,
                    radius_int == radius as int,
                    radius_int == k_int,
                    window_len_int == window_len as int,
                    window_len_int == 2 * radius_int + 1,
                    window_len <= n,
                    denom == window_len as i64,
                    limit == n - radius,
                    radius < limit <= n,
                    radius <= center <= limit,
                    forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 100_000,
                    result.len() == n,
                    forall |j: int| 0 <= j < radius_int ==> #[trigger] result@[j] == -1,
                    forall |j: int| radius_int <= j < center as int ==> #[trigger] result@[j] as int == Self::window_sum(nums@, j - radius_int, window_len_int) / window_len_int,
                    forall |j: int| center as int <= j < n_int ==> #[trigger] result@[j] == -1,
                    center < limit ==> sum as int == Self::window_sum(nums@, center as int - radius_int, window_len_int),
                    0 <= sum as int <= window_len_int * 100_000,
                decreases limit - center,
            {
                let ghost center_int = center as int;
                proof {
                    Self::lemma_window_sum_nonneg(nums@, center_int - radius_int, window_len_int);
                    Self::lemma_window_sum_upper(nums@, center_int - radius_int, window_len_int);
                    assert(0 < window_len_int);
                    assert(0 <= sum as int / window_len_int <= 100_000) by (nonlinear_arith)
                        requires
                            0 <= sum as int,
                            sum as int <= window_len_int * 100_000,
                            0 < window_len_int,
                    {};
                }
                let avg = (sum / denom) as i32;
                proof {
                    assert(avg as int == sum as int / window_len_int);
                    assert(avg as int == Self::window_sum(nums@, center_int - radius_int, window_len_int) / window_len_int);
                }
                let ghost old_result = result@;
                result.set(center, avg);
                proof {
                    assert(result@ == old_result.update(center_int, avg));
                    assert forall |j: int| 0 <= j < radius_int implies #[trigger] result@[j] == -1 by {
                        assert(result@[j] == old_result[j]);
                    }
                    assert forall |j: int| radius_int <= j < center_int + 1 implies #[trigger] result@[j] as int == Self::window_sum(nums@, j - radius_int, window_len_int) / window_len_int by {
                        if j < center_int {
                            assert(result@[j] == old_result[j]);
                        } else {
                            assert(j == center_int);
                        }
                    }
                    assert forall |j: int| center_int + 1 <= j < n_int implies #[trigger] result@[j] == -1 by {
                        assert(result@[j] == old_result[j]);
                    }
                }
                if center + 1 < limit {
                    let ghost old_sum = sum as int;
                    sum += nums[center + radius + 1] as i64;
                    sum -= nums[center - radius] as i64;
                    proof {
                        Self::lemma_window_slide(nums@, center_int - radius_int, window_len_int);
                        assert(old_sum == Self::window_sum(nums@, center_int - radius_int, window_len_int));
                        assert(sum as int == old_sum + nums[center_int + radius_int + 1] as int - nums[center_int - radius_int] as int);
                        assert(sum as int == Self::window_sum(nums@, center_int + 1 - radius_int, window_len_int));
                        Self::lemma_window_sum_nonneg(nums@, center_int + 1 - radius_int, window_len_int);
                        Self::lemma_window_sum_upper(nums@, center_int + 1 - radius_int, window_len_int);
                    }
                }
                center += 1;
            }

            result
        }
    }
}

}

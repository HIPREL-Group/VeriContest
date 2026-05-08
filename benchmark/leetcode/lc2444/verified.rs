use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_range(x: int, min_k: int, max_k: int) -> bool {
        min_k <= x && x <= max_k
    }

    pub open spec fn last_bad(nums: Seq<i32>, min_k: int, max_k: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            -1
        } else if !Self::in_range(nums[n - 1] as int, min_k, max_k) {
            n - 1
        } else {
            Self::last_bad(nums, min_k, max_k, n - 1)
        }
    }

    pub open spec fn last_pos(nums: Seq<i32>, target: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            -1
        } else if nums[n - 1] as int == target {
            n - 1
        } else {
            Self::last_pos(nums, target, n - 1)
        }
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    pub open spec fn end_count(nums: Seq<i32>, min_k: int, max_k: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
    {
        if n <= 0 {
            0
        } else {
            let bad = Self::last_bad(nums, min_k, max_k, n);
            let bound = Self::min_int(
                Self::last_pos(nums, min_k, n),
                Self::last_pos(nums, max_k, n),
            );
            if bound > bad {
                bound - bad
            } else {
                0
            }
        }
    }

    pub open spec fn count_fixed_bound_subarrays(nums: Seq<i32>, min_k: int, max_k: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_fixed_bound_subarrays(nums, min_k, max_k, n - 1)
                + Self::end_count(nums, min_k, max_k, n)
        }
    }

    proof fn lemma_last_bad_step(nums: Seq<i32>, min_k: int, max_k: int, n: int)
        requires
            0 <= n && n < nums.len(),
        ensures
            Self::last_bad(nums, min_k, max_k, n + 1)
                == if !Self::in_range(nums[n] as int, min_k, max_k) {
                    n
                } else {
                    Self::last_bad(nums, min_k, max_k, n)
                },
    {
        reveal_with_fuel(Solution::last_bad, 2);
    }

    proof fn lemma_last_pos_step(nums: Seq<i32>, target: int, n: int)
        requires
            0 <= n && n < nums.len(),
        ensures
            Self::last_pos(nums, target, n + 1)
                == if nums[n] as int == target {
                    n
                } else {
                    Self::last_pos(nums, target, n)
                },
    {
        reveal_with_fuel(Solution::last_pos, 2);
    }

    pub fn count_subarrays(nums: Vec<i32>, min_k: i32, max_k: i32) -> (result: i64)
        requires
            2 <= nums.len() && nums.len() <= 100_000,
            1 <= min_k && min_k <= 1_000_000,
            1 <= max_k && max_k <= 1_000_000,
            forall|i: int| 0 <= i && i < nums.len() ==> 1 <= nums[i] && nums[i] <= 1_000_000,
        ensures
            result >= 0,
            result as int == Self::count_fixed_bound_subarrays(nums@, min_k as int, max_k as int, nums.len() as int),
    {
        let n = nums.len();
        let mut result: i64 = 0;
        let mut last_bad: i64 = -1;
        let mut last_min: i64 = -1;
        let mut last_max: i64 = -1;
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                2 <= n && n <= 100_000,
                1 <= min_k && min_k <= 1_000_000,
                1 <= max_k && max_k <= 1_000_000,
                forall|j: int| 0 <= j && j < n ==> 1 <= nums@[j] && nums@[j] <= 1_000_000,
                0 <= i && i <= n,
                -1 <= last_bad,
                last_bad < i as i64,
                -1 <= last_min,
                last_min < i as i64,
                -1 <= last_max,
                last_max < i as i64,
                last_bad as int == Self::last_bad(nums@, min_k as int, max_k as int, i as int),
                last_min as int == Self::last_pos(nums@, min_k as int, i as int),
                last_max as int == Self::last_pos(nums@, max_k as int, i as int),
                result >= 0,
                result as int == Self::count_fixed_bound_subarrays(nums@, min_k as int, max_k as int, i as int),
                result as int <= i as int * (i as int + 1) / 2,
            decreases n - i,
        {
            let prev_bad = last_bad;
            let prev_min = last_min;
            let prev_max = last_max;
            let value = nums[i];
            if value < min_k || value > max_k {
                last_bad = i as i64;
            }
            if value == min_k {
                last_min = i as i64;
            }
            if value == max_k {
                last_max = i as i64;
            }
            let bound = if last_min < last_max {
                last_min
            } else {
                last_max
            };
            let add = if bound > last_bad { bound - last_bad } else { 0 };

            proof {
                let k = i as int;
                assert(value as int == nums@[k] as int);

                Self::lemma_last_bad_step(nums@, min_k as int, max_k as int, k);
                if value < min_k || value > max_k {
                    assert(!Self::in_range(nums@[k] as int, min_k as int, max_k as int));
                    assert(Self::last_bad(nums@, min_k as int, max_k as int, k + 1) == k);
                    assert(last_bad as int == k);
                } else {
                    assert(Self::in_range(nums@[k] as int, min_k as int, max_k as int));
                    assert(Self::last_bad(nums@, min_k as int, max_k as int, k + 1)
                        == Self::last_bad(nums@, min_k as int, max_k as int, k));
                    assert(prev_bad as int == Self::last_bad(nums@, min_k as int, max_k as int, k));
                    assert(last_bad == prev_bad);
                }
                assert(last_bad as int == Self::last_bad(nums@, min_k as int, max_k as int, k + 1));

                Self::lemma_last_pos_step(nums@, min_k as int, k);
                if value == min_k {
                    assert(Self::last_pos(nums@, min_k as int, k + 1) == k);
                    assert(last_min as int == k);
                } else {
                    assert(Self::last_pos(nums@, min_k as int, k + 1)
                        == Self::last_pos(nums@, min_k as int, k));
                    assert(prev_min as int == Self::last_pos(nums@, min_k as int, k));
                    assert(last_min == prev_min);
                }
                assert(last_min as int == Self::last_pos(nums@, min_k as int, k + 1));

                Self::lemma_last_pos_step(nums@, max_k as int, k);
                if value == max_k {
                    assert(Self::last_pos(nums@, max_k as int, k + 1) == k);
                    assert(last_max as int == k);
                } else {
                    assert(Self::last_pos(nums@, max_k as int, k + 1)
                        == Self::last_pos(nums@, max_k as int, k));
                    assert(prev_max as int == Self::last_pos(nums@, max_k as int, k));
                    assert(last_max == prev_max);
                }
                assert(last_max as int == Self::last_pos(nums@, max_k as int, k + 1));

                reveal(Solution::end_count);
                assert(Self::min_int(last_min as int, last_max as int) == bound as int);
                if bound > last_bad {
                    assert(add == bound - last_bad);
                    assert(Self::end_count(nums@, min_k as int, max_k as int, k + 1)
                        == bound as int - last_bad as int);
                    assert(add as int == Self::end_count(nums@, min_k as int, max_k as int, k + 1));
                } else {
                    assert(add == 0);
                    assert(Self::end_count(nums@, min_k as int, max_k as int, k + 1) == 0);
                    assert(add as int == Self::end_count(nums@, min_k as int, max_k as int, k + 1));
                }

                reveal_with_fuel(Solution::count_fixed_bound_subarrays, 2);
                assert(Self::count_fixed_bound_subarrays(nums@, min_k as int, max_k as int, k + 1)
                    == Self::count_fixed_bound_subarrays(nums@, min_k as int, max_k as int, k)
                        + Self::end_count(nums@, min_k as int, max_k as int, k + 1));
                assert(result as int + add as int
                    == Self::count_fixed_bound_subarrays(nums@, min_k as int, max_k as int, k + 1));

                assert(bound <= i as i64);
                if bound > last_bad {
                    assert(add as int == bound as int - last_bad as int);
                    assert(bound as int - last_bad as int <= k + 1) by (nonlinear_arith)
                        requires
                            bound as int <= k,
                            -1 <= last_bad as int,
                    {};
                    assert(add as int <= k + 1);
                } else {
                    assert(add as int == 0);
                }
                assert(add as int >= 0);
                assert(result as int + add as int <= (k + 1) * (k + 2) / 2) by (nonlinear_arith)
                    requires
                        result as int <= k * (k + 1) / 2,
                        add as int <= k + 1,
                {};
                assert((k + 1) * (k + 2) / 2 <= 5_000_050_000) by (nonlinear_arith)
                    requires
                        0 <= k,
                        k + 1 <= 100_000,
                {};
                assert(result as int + add as int <= 9_223_372_036_854_775_807int) by (nonlinear_arith)
                    requires
                        result as int + add as int <= 5_000_050_000,
                {};
            }

            result = result + add;
            i = i + 1;
        }

        result
    }
}

}

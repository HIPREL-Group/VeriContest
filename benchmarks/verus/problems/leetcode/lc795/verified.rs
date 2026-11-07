use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_len_at_most(nums: Seq<i32>, bound: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else if nums[n - 1] as int <= bound {
            Self::suffix_len_at_most(nums, bound, n - 1) + 1
        } else {
            0
        }
    }

    pub open spec fn count_at_most(nums: Seq<i32>, bound: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_at_most(nums, bound, n - 1)
                + Self::suffix_len_at_most(nums, bound, n)
        }
    }

    pub open spec fn count_bounded_max(nums: Seq<i32>, left: int, right: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
            left <= right,
    {
        Self::count_at_most(nums, right, n) - Self::count_at_most(nums, left - 1, n)
    }

    proof fn lemma_suffix_len_step(nums: Seq<i32>, bound: int, n: int)
        requires
            0 <= n < nums.len(),
        ensures
            Self::suffix_len_at_most(nums, bound, n + 1)
                == if nums[n] as int <= bound {
                    Self::suffix_len_at_most(nums, bound, n) + 1
                } else {
                    0
                },
    {
        reveal_with_fuel(Solution::suffix_len_at_most, 2);
    }

    proof fn lemma_count_at_most_step(nums: Seq<i32>, bound: int, n: int)
        requires
            0 <= n < nums.len(),
        ensures
            Self::count_at_most(nums, bound, n + 1)
                == Self::count_at_most(nums, bound, n)
                    + Self::suffix_len_at_most(nums, bound, n + 1),
    {
        reveal_with_fuel(Solution::count_at_most, 2);
    }

    proof fn lemma_suffix_len_mono(nums: Seq<i32>, lower: int, upper: int, n: int)
        requires
            0 <= n <= nums.len(),
            lower <= upper,
        ensures
            Self::suffix_len_at_most(nums, lower, n) <= Self::suffix_len_at_most(nums, upper, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_suffix_len_mono(nums, lower, upper, n - 1);
            Self::lemma_suffix_len_step(nums, lower, n - 1);
            Self::lemma_suffix_len_step(nums, upper, n - 1);
            if nums[n - 1] as int <= lower {
                assert(nums[n - 1] as int <= upper);
                assert(Self::suffix_len_at_most(nums, lower, n)
                    == Self::suffix_len_at_most(nums, lower, n - 1) + 1);
                assert(Self::suffix_len_at_most(nums, upper, n)
                    == Self::suffix_len_at_most(nums, upper, n - 1) + 1);
            } else {
                assert(Self::suffix_len_at_most(nums, lower, n) == 0);
                Self::lemma_suffix_len_nonneg(nums, upper, n);
            }
        }
    }

    proof fn lemma_suffix_len_nonneg(nums: Seq<i32>, bound: int, n: int)
        requires
            0 <= n <= nums.len(),
        ensures
            0 <= Self::suffix_len_at_most(nums, bound, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_suffix_len_step(nums, bound, n - 1);
            if nums[n - 1] as int <= bound {
                Self::lemma_suffix_len_nonneg(nums, bound, n - 1);
            }
        }
    }

    proof fn lemma_count_at_most_mono(nums: Seq<i32>, lower: int, upper: int, n: int)
        requires
            0 <= n <= nums.len(),
            lower <= upper,
        ensures
            Self::count_at_most(nums, lower, n) <= Self::count_at_most(nums, upper, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_count_at_most_mono(nums, lower, upper, n - 1);
            Self::lemma_suffix_len_mono(nums, lower, upper, n);
            Self::lemma_count_at_most_step(nums, lower, n - 1);
            Self::lemma_count_at_most_step(nums, upper, n - 1);
            assert(Self::count_at_most(nums, lower, n)
                == Self::count_at_most(nums, lower, n - 1)
                    + Self::suffix_len_at_most(nums, lower, n));
            assert(Self::count_at_most(nums, upper, n)
                == Self::count_at_most(nums, upper, n - 1)
                    + Self::suffix_len_at_most(nums, upper, n));
        }
    }

    fn count_at_most_exec(nums: &Vec<i32>, bound: i32) -> (ans: i64)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            ans >= 0,
            ans as int == Self::count_at_most(nums@, bound as int, nums.len() as int),
            ans as int <= nums.len() as int * (nums.len() as int + 1) / 2,
    {
        let n = nums.len();
        let ghost s = nums@;
        let mut ans: i64 = 0;
        let mut cnt: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                s == nums@,
                1 <= n <= 100_000,
                forall |j: int| 0 <= j < n ==> 0 <= #[trigger] nums@[j] <= 1_000_000_000,
                0 <= i <= n,
                0 <= cnt <= i,
                cnt as int == Self::suffix_len_at_most(s, bound as int, i as int),
                ans >= 0,
                ans as int == Self::count_at_most(s, bound as int, i as int),
                ans as int <= i as int * (i as int + 1) / 2,
            decreases n - i,
        {
            let prev_ans = ans;
            let prev_cnt = cnt;
            let value = nums[i];

            proof {
                assert(value as int == s[i as int] as int);
                assert((i as int) < n);
                assert((i as int) < 100_000);
            }

            if value <= bound {
                proof {
                    assert((prev_cnt as int) + 1 <= 100_000) by (nonlinear_arith)
                        requires
                            (prev_cnt as int) <= (i as int),
                            (i as int) < 100_000,
                    {};
                    assert(prev_cnt < i64::MAX);
                }
                cnt = cnt + 1;
            } else {
                cnt = 0;
            }

            proof {
                Self::lemma_suffix_len_step(s, bound as int, i as int);
                if value <= bound {
                    assert(Self::suffix_len_at_most(s, bound as int, i as int + 1)
                        == Self::suffix_len_at_most(s, bound as int, i as int) + 1);
                    assert((prev_cnt as int) == Self::suffix_len_at_most(s, bound as int, i as int));
                    assert((cnt as int) == Self::suffix_len_at_most(s, bound as int, i as int + 1));
                    assert((cnt as int) <= (i as int) + 1) by (nonlinear_arith)
                        requires
                            (prev_cnt as int) <= (i as int),
                            (cnt as int) == (prev_cnt as int) + 1,
                    {};
                } else {
                    assert(Self::suffix_len_at_most(s, bound as int, i as int + 1) == 0);
                    assert((cnt as int) == 0);
                }

                Self::lemma_count_at_most_step(s, bound as int, i as int);
                assert((prev_ans as int) == Self::count_at_most(s, bound as int, i as int));
                assert((prev_ans as int) + (cnt as int)
                    == Self::count_at_most(s, bound as int, i as int + 1));
                assert((prev_ans as int) + (cnt as int)
                    <= ((i as int) + 1) * ((i as int) + 2) / 2) by (nonlinear_arith)
                    requires
                        (prev_ans as int) <= (i as int) * ((i as int) + 1) / 2,
                        0 <= (cnt as int) <= (i as int) + 1,
                {};
                assert(((i as int) + 1) * ((i as int) + 2) / 2 <= 5_000_050_000) by (nonlinear_arith)
                    requires
                        (i as int) < 100_000,
                {};
                assert((prev_ans as int) + (cnt as int) <= 9_223_372_036_854_775_807int) by (nonlinear_arith)
                    requires
                        (prev_ans as int) + (cnt as int) <= 5_000_050_000,
                {};
            }

            ans = ans + cnt;

            proof {
                assert((ans as int) == Self::count_at_most(s, bound as int, i as int + 1));
                assert((ans as int) <= ((i as int) + 1) * ((i as int) + 2) / 2);
            }

            i = i + 1;
        }
        ans
    }

    pub fn num_subarray_bounded_max(nums: Vec<i32>, left: i32, right: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= left <= right <= 1_000_000_000,
            Self::count_bounded_max(nums@, left as int, right as int, nums.len() as int) <= i32::MAX,
        ensures
            res as int == Self::count_bounded_max(nums@, left as int, right as int, nums.len() as int),
    {
        let upper = Self::count_at_most_exec(&nums, right);
        let lower = Self::count_at_most_exec(&nums, left - 1);

        proof {
            assert(left as int - 1 <= right as int);
            Self::lemma_count_at_most_mono(nums@, left as int - 1, right as int, nums.len() as int);
            assert(lower as int <= upper as int);
        }

        let result = upper - lower;

        proof {
            assert(result as int == upper as int - lower as int);
            assert(result as int
                == Self::count_at_most(nums@, right as int, nums.len() as int)
                    - Self::count_at_most(nums@, left as int - 1, nums.len() as int));
            assert(result as int
                == Self::count_bounded_max(nums@, left as int, right as int, nums.len() as int));
            assert(0 <= result as int);
            assert(result as int <= i32::MAX);
        }

        result as i32
    }
}

}

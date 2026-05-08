use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn imin(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn sub_or(nums: Seq<i32>, start: int, end: int) -> i32
        decreases end - start,
    {
        if end <= start {
            0i32
        } else {
            Self::sub_or(nums, start, end - 1) | nums[end - 1]
        }
    }

    pub open spec fn min_len_start_upto(nums: Seq<i32>, k: i32, start: int, upto: int) -> int
        decreases upto - start,
    {
        if upto <= start {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_start_upto(nums, k, start, upto - 1);
            let cand = if Self::sub_or(nums, start, upto) >= k {
                upto - start
            } else {
                nums.len() as int + 1
            };
            Self::imin(prev, cand)
        }
    }

    pub open spec fn min_len_prefix(nums: Seq<i32>, k: i32, processed: int) -> int
        decreases processed,
    {
        if processed <= 0 {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_prefix(nums, k, processed - 1);
            let cur = Self::min_len_start_upto(nums, k, processed - 1, nums.len() as int);
            Self::imin(prev, cur)
        }
    }

    pub open spec fn minimum_subarray_length_spec(nums: Seq<i32>, k: i32) -> int {
        let best = Self::min_len_prefix(nums, k, nums.len() as int);
        if best <= nums.len() as int { best } else { -1 }
    }

    proof fn lemma_sub_or_extend(nums: Seq<i32>, start: int, end: int)
        requires
            0 <= start <= end < nums.len(),
        ensures
            Self::sub_or(nums, start, end + 1) == (Self::sub_or(nums, start, end) | nums[end]),
    {
        reveal_with_fuel(Solution::sub_or, 2);
    }

    pub fn minimum_subarray_length(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 200000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= k <= 1_000_000_000,
        ensures
            result as int == Self::minimum_subarray_length_spec(nums@, k),
    {
        let n = nums.len();
        let mut ans: i32 = n as i32 + 1;
        let mut i: usize = 0;

        while i < n
            invariant
                1 <= n <= 200000,
                n == nums.len(),
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
                0 <= k <= 1_000_000_000,
                0 <= i <= n,
                1 <= ans <= n as i32 + 1,
                ans as int == Self::min_len_prefix(nums@, k, i as int),
            decreases n - i,
        {
            let mut cur_or: i32 = 0;
            let mut j: usize = i;
            let mut best_i: i32 = n as i32 + 1;

            while j < n
                invariant
                    1 <= n <= 200000,
                    n == nums.len(),
                    forall |t: int| 0 <= t < nums.len() ==> 0 <= #[trigger] nums[t] <= 1_000_000_000,
                    0 <= k <= 1_000_000_000,
                    0 <= i < n,
                    i <= j <= n,
                    1 <= best_i <= n as i32 + 1,
                    cur_or == Self::sub_or(nums@, i as int, j as int),
                    best_i as int == Self::min_len_start_upto(nums@, k, i as int, j as int),
                decreases n - j,
            {
                cur_or = cur_or | nums[j];

                let cand: i32;
                if cur_or >= k {
                    cand = (j - i + 1) as i32;
                } else {
                    cand = n as i32 + 1;
                }

                let ghost old_best = best_i as int;
                if cand < best_i {
                    best_i = cand;
                }

                proof {
                    Self::lemma_sub_or_extend(nums@, i as int, j as int);
                    assert(cur_or == Self::sub_or(nums@, i as int, (j + 1) as int));

                    assert(Self::min_len_start_upto(nums@, k, i as int, (j + 1) as int)
                        == Self::imin(
                            Self::min_len_start_upto(nums@, k, i as int, j as int),
                            if Self::sub_or(nums@, i as int, (j + 1) as int) >= k {
                                (j + 1) as int - i as int
                            } else {
                                n as int + 1
                            }
                        ));
                    assert(old_best == Self::min_len_start_upto(nums@, k, i as int, j as int));
                    assert(cand as int
                        == if Self::sub_or(nums@, i as int, (j + 1) as int) >= k {
                            (j + 1) as int - i as int
                        } else {
                            n as int + 1
                        });
                    if cand < old_best as i32 {
                        assert(best_i as int == cand as int);
                    } else {
                        assert(best_i as int == old_best);
                    }
                    assert(best_i as int == Self::imin(old_best, cand as int));
                }

                j = j + 1;
            }

            if best_i < ans {
                ans = best_i;
            }

            proof {
                assert(j == n);
                assert(ans as int
                    == Self::imin(Self::min_len_prefix(nums@, k, i as int), Self::min_len_start_upto(nums@, k, i as int, n as int)));
                assert(Self::min_len_prefix(nums@, k, (i + 1) as int)
                    == Self::imin(Self::min_len_prefix(nums@, k, i as int), Self::min_len_start_upto(nums@, k, i as int, n as int)));
                assert(ans as int == Self::min_len_prefix(nums@, k, (i + 1) as int));
            }

            i = i + 1;
        }

        if ans <= n as i32 {
            ans
        } else {
            -1
        }
    }
}

}

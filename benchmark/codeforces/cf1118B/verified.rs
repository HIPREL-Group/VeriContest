use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn odd_sum_before(nums: Seq<i64>, end_pos: int) -> int
        recommends
            0 <= end_pos <= nums.len(),
        decreases end_pos,
    {
        if end_pos <= 0 {
            0
        } else {
            Self::odd_sum_before(nums, end_pos - 1) + if end_pos % 2 == 1 {
                nums[end_pos - 1] as int
            } else {
                0
            }
        }
    }

    pub open spec fn even_sum_before(nums: Seq<i64>, end_pos: int) -> int
        recommends
            0 <= end_pos <= nums.len(),
        decreases end_pos,
    {
        if end_pos <= 0 {
            0
        } else {
            Self::even_sum_before(nums, end_pos - 1) + if end_pos % 2 == 0 {
                nums[end_pos - 1] as int
            } else {
                0
            }
        }
    }

    pub open spec fn odd_sum_after(nums: Seq<i64>, start_idx: int) -> int
        recommends
            0 <= start_idx <= nums.len(),
        decreases nums.len() as int - start_idx,
    {
        if start_idx >= nums.len() as int {
            0
        } else {
            let new_pos = start_idx;
            (if new_pos % 2 == 1 { nums[start_idx] as int } else { 0 })
                + Self::odd_sum_after(nums, start_idx + 1)
        }
    }

    pub open spec fn even_sum_after(nums: Seq<i64>, start_idx: int) -> int
        recommends
            0 <= start_idx <= nums.len(),
        decreases nums.len() as int - start_idx,
    {
        if start_idx >= nums.len() as int {
            0
        } else {
            let new_pos = start_idx;
            (if new_pos % 2 == 0 { nums[start_idx] as int } else { 0 })
                + Self::even_sum_after(nums, start_idx + 1)
        }
    }

    pub open spec fn odd_day_sum_after_removal(nums: Seq<i64>, remove_pos: int) -> int
        recommends
            1 <= remove_pos <= nums.len(),
    {
        let remove_idx = remove_pos - 1;
        Self::odd_sum_before(nums, remove_idx) + Self::odd_sum_after(nums, remove_pos)
    }

    pub open spec fn even_day_sum_after_removal(nums: Seq<i64>, remove_pos: int) -> int
        recommends
            1 <= remove_pos <= nums.len(),
    {
        let remove_idx = remove_pos - 1;
        Self::even_sum_before(nums, remove_idx) + Self::even_sum_after(nums, remove_pos)
    }

    pub open spec fn is_good_candy(nums: Seq<i64>, i: int) -> bool
        recommends
            1 <= i <= nums.len(),
    {
        Self::odd_day_sum_after_removal(nums, i) == Self::even_day_sum_after_removal(nums, i)
    }

    pub open spec fn count_good_candies_upto(nums: Seq<i64>, i_end: int) -> nat
        recommends
            0 <= i_end <= nums.len(),
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            Self::count_good_candies_upto(nums, i_end - 1) + if Self::is_good_candy(nums, i_end) {
                1nat
            } else {
                0nat
            }
        }
    }

    pub open spec fn count_good_candies(nums: Seq<i64>) -> nat {
        Self::count_good_candies_upto(nums, nums.len() as int)
    }

    pub open spec fn sum_even_indices(nums: Seq<i64>, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let last = end - 1;
            Self::sum_even_indices(nums, last) + if last % 2 == 0 { nums[last] as int } else { 0 }
        }
    }

    pub open spec fn sum_odd_indices(nums: Seq<i64>, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let last = end - 1;
            Self::sum_odd_indices(nums, last) + if last % 2 == 1 { nums[last] as int } else { 0 }
        }
    }

    proof fn lemma_odd_before_eq_sum_even(nums: Seq<i64>, end_pos: int)
        requires
            0 <= end_pos <= nums.len(),
        ensures
            Self::odd_sum_before(nums, end_pos) == Self::sum_even_indices(nums, end_pos),
        decreases end_pos,
    {
        if end_pos <= 0 {
            reveal_with_fuel(Solution::odd_sum_before, 2);
            reveal_with_fuel(Solution::sum_even_indices, 2);
        } else {
            Self::lemma_odd_before_eq_sum_even(nums, end_pos - 1);
            reveal_with_fuel(Solution::odd_sum_before, 2);
            reveal_with_fuel(Solution::sum_even_indices, 2);
        }
    }

    proof fn lemma_even_before_eq_sum_odd(nums: Seq<i64>, end_pos: int)
        requires
            0 <= end_pos <= nums.len(),
        ensures
            Self::even_sum_before(nums, end_pos) == Self::sum_odd_indices(nums, end_pos),
        decreases end_pos,
    {
        if end_pos <= 0 {
            reveal_with_fuel(Solution::even_sum_before, 2);
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        } else {
            Self::lemma_even_before_eq_sum_odd(nums, end_pos - 1);
            reveal_with_fuel(Solution::even_sum_before, 2);
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        }
    }

    proof fn lemma_sum_odd_step(nums: Seq<i64>, i: int)
        requires
            0 <= i < nums.len(),
        ensures
            Self::sum_odd_indices(nums, i + 1)
                == Self::sum_odd_indices(nums, i) + if i % 2 == 1 { nums[i] as int } else { 0 },
    {
        reveal_with_fuel(Solution::sum_odd_indices, 2);
    }

    proof fn lemma_sum_even_step(nums: Seq<i64>, i: int)
        requires
            0 <= i < nums.len(),
        ensures
            Self::sum_even_indices(nums, i + 1)
                == Self::sum_even_indices(nums, i) + if i % 2 == 0 { nums[i] as int } else { 0 },
    {
        reveal_with_fuel(Solution::sum_even_indices, 2);
    }

    proof fn lemma_odd_sum_after_eq_delta(nums: Seq<i64>, start: int)
        requires
            0 <= start <= nums.len(),
        ensures
            Self::odd_sum_after(nums, start)
                == Self::sum_odd_indices(nums, nums.len() as int) - Self::sum_odd_indices(nums, start),
        decreases nums.len() as int - start,
    {
        let n = nums.len() as int;
        if start >= n {
            reveal_with_fuel(Solution::odd_sum_after, 2);
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        } else {
            Self::lemma_odd_sum_after_eq_delta(nums, start + 1);
            reveal_with_fuel(Solution::odd_sum_after, 2);
            Self::lemma_sum_odd_step(nums, start);
        }
    }

    proof fn lemma_even_sum_after_eq_delta(nums: Seq<i64>, start: int)
        requires
            0 <= start <= nums.len(),
        ensures
            Self::even_sum_after(nums, start)
                == Self::sum_even_indices(nums, nums.len() as int) - Self::sum_even_indices(nums, start),
        decreases nums.len() as int - start,
    {
        let n = nums.len() as int;
        if start >= n {
            reveal_with_fuel(Solution::even_sum_after, 2);
            reveal_with_fuel(Solution::sum_even_indices, 2);
        } else {
            Self::lemma_even_sum_after_eq_delta(nums, start + 1);
            reveal_with_fuel(Solution::even_sum_after, 2);
            Self::lemma_sum_even_step(nums, start);
        }
    }

    proof fn lemma_odd_tail_closed(nums: Seq<i64>, i: int, total_odd: int, pe: int)
        requires
            0 <= i < nums.len(),
            total_odd == Self::sum_odd_indices(nums, nums.len() as int),
            pe == Self::sum_odd_indices(nums, i),
        ensures
            total_odd - pe - (if i % 2 == 1 { nums[i] as int } else { 0 })
                == Self::odd_sum_after(nums, i + 1),
    {
        Self::lemma_sum_odd_step(nums, i);
        Self::lemma_odd_sum_after_eq_delta(nums, i + 1);
        assert(Self::sum_odd_indices(nums, nums.len() as int) - Self::sum_odd_indices(nums, i)
            == (if i % 2 == 1 { nums[i] as int } else { 0 })
                + (Self::sum_odd_indices(nums, nums.len() as int) - Self::sum_odd_indices(nums, i + 1)));
    }

    proof fn lemma_even_tail_closed(nums: Seq<i64>, i: int, total_even: int, po: int)
        requires
            0 <= i < nums.len(),
            total_even == Self::sum_even_indices(nums, nums.len() as int),
            po == Self::sum_even_indices(nums, i),
        ensures
            total_even - po - (if i % 2 == 0 { nums[i] as int } else { 0 })
                == Self::even_sum_after(nums, i + 1),
    {
        Self::lemma_sum_even_step(nums, i);
        Self::lemma_even_sum_after_eq_delta(nums, i + 1);
        assert(Self::sum_even_indices(nums, nums.len() as int) - Self::sum_even_indices(nums, i)
            == (if i % 2 == 0 { nums[i] as int } else { 0 })
                + (Self::sum_even_indices(nums, nums.len() as int) - Self::sum_even_indices(nums, i + 1)));
    }

    proof fn lemma_sum_even_indices_bounded(nums: Seq<i64>, end: int)
        requires
            0 <= end <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
        ensures
            Self::sum_even_indices(nums, end) <= end * 10_000,
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_even_indices_bounded(nums, end - 1);
            reveal_with_fuel(Solution::sum_even_indices, 2);
            assert(nums[end - 1] as int <= 10_000);
        } else {
            reveal_with_fuel(Solution::sum_even_indices, 2);
        }
    }

    proof fn lemma_sum_odd_indices_bounded(nums: Seq<i64>, end: int)
        requires
            0 <= end <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
        ensures
            Self::sum_odd_indices(nums, end) <= end * 10_000,
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_odd_indices_bounded(nums, end - 1);
            reveal_with_fuel(Solution::sum_odd_indices, 2);
            assert(nums[end - 1] as int <= 10_000);
        } else {
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        }
    }

    proof fn lemma_sum_odd_prefix_le_total(nums: Seq<i64>, i: int, n: int)
        requires
            0 <= i <= n <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
        ensures
            Self::sum_odd_indices(nums, i) <= Self::sum_odd_indices(nums, n),
        decreases n - i,
    {
        if i < n {
            Self::lemma_sum_odd_prefix_le_total(nums, i + 1, n);
            Self::lemma_sum_odd_step(nums, i);
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        } else {
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        }
    }

    proof fn lemma_sum_even_prefix_le_total(nums: Seq<i64>, i: int, n: int)
        requires
            0 <= i <= n <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
        ensures
            Self::sum_even_indices(nums, i) <= Self::sum_even_indices(nums, n),
        decreases n - i,
    {
        if i < n {
            Self::lemma_sum_even_prefix_le_total(nums, i + 1, n);
            Self::lemma_sum_even_step(nums, i);
            reveal_with_fuel(Solution::sum_even_indices, 2);
        } else {
            reveal_with_fuel(Solution::sum_even_indices, 2);
        }
    }

    proof fn lemma_sum_odd_indices_nonneg(nums: Seq<i64>, end: int)
        requires
            0 <= end <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
        ensures
            Self::sum_odd_indices(nums, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_odd_indices_nonneg(nums, end - 1);
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        } else {
            reveal_with_fuel(Solution::sum_odd_indices, 2);
        }
    }

    proof fn lemma_sum_even_indices_nonneg(nums: Seq<i64>, end: int)
        requires
            0 <= end <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
        ensures
            Self::sum_even_indices(nums, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_even_indices_nonneg(nums, end - 1);
            reveal_with_fuel(Solution::sum_even_indices, 2);
        } else {
            reveal_with_fuel(Solution::sum_even_indices, 2);
        }
    }

    pub fn count_equal_sums(a: Vec<i64>) -> (result: i32)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 10_000,
        ensures
            result as int == Self::count_good_candies(a@),
    {
        let n = a.len();
        proof {
            assert(n == a@.len());
        }
        let mut total_even_idx = 0i64;
        let mut total_odd_idx = 0i64;
        let mut t = 0;
        while t < n
            invariant
                t <= n,
                n == a.len(),
                1 <= n <= 200_000,
                forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 10_000,
                total_even_idx as int == Self::sum_even_indices(a@, t as int),
                total_odd_idx as int == Self::sum_odd_indices(a@, t as int),
                -3_000_000_000i64 <= total_even_idx <= 3_000_000_000i64,
                -3_000_000_000i64 <= total_odd_idx <= 3_000_000_000i64,
            decreases n - t,
        {
            proof {
                assert((t as int) < a@.len());
                Self::lemma_sum_even_indices_bounded(a@, t as int);
                Self::lemma_sum_odd_indices_bounded(a@, t as int);
                assert((total_even_idx as int) + 10000 <= 3_000_000_000);
                assert((total_odd_idx as int) + 10000 <= 3_000_000_000);
            }
            if t % 2 == 0 {
                total_even_idx = total_even_idx + a[t];
            } else {
                total_odd_idx = total_odd_idx + a[t];
            }
            proof {
                Self::lemma_sum_even_step(a@, t as int);
                Self::lemma_sum_odd_step(a@, t as int);
                reveal_with_fuel(Solution::sum_even_indices, 10);
                reveal_with_fuel(Solution::sum_odd_indices, 10);
                assert(total_even_idx as int == Self::sum_even_indices(a@, (t + 1) as int));
                assert(total_odd_idx as int == Self::sum_odd_indices(a@, (t + 1) as int));
            }
            t = t + 1;
        }
        let mut po = 0i64;
        let mut pe = 0i64;
        let mut count = 0i32;
        let mut i = 0;
        while i < n
            invariant
                i <= n,
                n == a.len(),
                1 <= n <= 200_000,
                forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 10_000,
                po as int == Self::sum_even_indices(a@, i as int),
                pe as int == Self::sum_odd_indices(a@, i as int),
                total_even_idx as int == Self::sum_even_indices(a@, n as int),
                total_odd_idx as int == Self::sum_odd_indices(a@, n as int),
                count as int == Self::count_good_candies_upto(a@, i as int),
                count as int <= i as int + 1,
                -3_000_000_000i64 <= total_even_idx <= 3_000_000_000i64,
                -3_000_000_000i64 <= total_odd_idx <= 3_000_000_000i64,
            decreases n - i,
        {
            proof {
                assert((i as int) < (a@.len() as int));
                Self::lemma_sum_odd_prefix_le_total(a@, i as int, a@.len() as int);
                Self::lemma_sum_even_prefix_le_total(a@, i as int, a@.len() as int);
                assert(pe as int <= total_odd_idx as int);
                assert(po as int <= total_even_idx as int);
                Self::lemma_sum_odd_indices_bounded(a@, a@.len() as int);
                Self::lemma_sum_even_indices_bounded(a@, a@.len() as int);
                Self::lemma_sum_odd_indices_nonneg(a@, i as int);
                Self::lemma_sum_even_indices_nonneg(a@, i as int);
                assert(pe as int >= 0);
                assert(po as int >= 0);
                assert(total_odd_idx as int <= (a@.len() as int) * 10000);
                assert(total_even_idx as int <= (a@.len() as int) * 10000);
                assert((total_odd_idx as int) - (pe as int) <= total_odd_idx as int);
                assert((total_even_idx as int) - (po as int) <= total_even_idx as int);
                assert((a@.len() as int) * 10000 < 9223372036854775807);
            }
            let odd_tail = total_odd_idx - pe - if i % 2 == 1 { a[i] } else { 0 };
            let even_tail = total_even_idx - po - if i % 2 == 0 { a[i] } else { 0 };
            let odd_sum = po + odd_tail;
            let even_sum = pe + even_tail;
            proof {
                Self::lemma_odd_before_eq_sum_even(a@, i as int);
                Self::lemma_even_before_eq_sum_odd(a@, i as int);
                Self::lemma_odd_tail_closed(a@, i as int, total_odd_idx as int, pe as int);
                Self::lemma_even_tail_closed(a@, i as int, total_even_idx as int, po as int);
                assert(odd_sum as int == Self::odd_day_sum_after_removal(a@, (i + 1) as int));
                assert(even_sum as int == Self::even_day_sum_after_removal(a@, (i + 1) as int));
            }
            if odd_sum == even_sum {
                proof {
                    assert((count as int) + 1 <= 300_000);
                }
                count = count + 1;
            }
            proof {
                reveal_with_fuel(Solution::count_good_candies_upto, 2);
            }
            if i % 2 == 0 {
                po = po + a[i];
            } else {
                pe = pe + a[i];
            }
            proof {
                Self::lemma_sum_even_step(a@, i as int);
                Self::lemma_sum_odd_step(a@, i as int);
            }
            i = i + 1;
        }
        count
    }
}

}

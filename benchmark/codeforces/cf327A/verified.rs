use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_ones(nums: Seq<i32>, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            Self::count_ones(nums, start + 1, end) + if nums[start] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn total_ones(nums: Seq<i32>) -> int {
        Self::count_ones(nums, 0, nums.len() as int)
    }

    pub open spec fn flip_value(x: i32) -> i32 {
        (1int - x as int) as i32
    }

    pub open spec fn after_flip(nums: Seq<i32>, i: int, j: int, k: int) -> i32
        recommends
            0 <= i <= j < nums.len(),
            0 <= k < nums.len(),
    {
        if i <= k && k <= j {
            Self::flip_value(nums[k])
        } else {
            nums[k]
        }
    }

    pub open spec fn count_ones_after_flip(nums: Seq<i32>, i: int, j: int, end: int) -> int
        recommends
            0 <= i <= j < nums.len(),
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_ones_after_flip(nums, i, j, end - 1) + if Self::after_flip(nums, i, j, end - 1) == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn count_ones_after_flip_window(nums: Seq<i32>, i: int, j: int) -> int
        recommends
            0 <= i <= j < nums.len(),
    {
        Self::count_ones_after_flip(nums, i, j, nums.len() as int)
    }

    pub open spec fn max_ones_over_windows(nums: Seq<i32>, i: int, j_end: int) -> int
        recommends
            0 <= i <= j_end <= nums.len(),
        decreases j_end - i,
    {
        if i >= j_end {
            0
        } else {
            let current = Self::count_ones_after_flip_window(nums, i, j_end - 1);
            let rest = Self::max_ones_over_windows(nums, i, j_end - 1);
            if current > rest { current } else { rest }
        }
    }

    pub open spec fn max_ones_all_windows(nums: Seq<i32>, i_end: int) -> int
        recommends
            0 <= i_end <= nums.len(),
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            let current_row = Self::max_ones_over_windows(nums, i_end - 1, nums.len() as int);
            let rest = Self::max_ones_all_windows(nums, i_end - 1);
            if current_row > rest { current_row } else { rest }
        }
    }

    pub open spec fn max_ones_after_one_flip(nums: Seq<i32>) -> int {
        if nums.len() == 0 {
            0
        } else {
            Self::max_ones_all_windows(nums, nums.len() as int)
        }
    }

    proof fn lemma_count_nonneg(nums: Seq<i32>, i: int, j: int, end: int)
        requires 0 <= end,
        ensures Self::count_ones_after_flip(nums, i, j, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_nonneg(nums, i, j, end - 1);
        }
    }

    proof fn lemma_mow_bound(nums: Seq<i32>, i: int, j_end: int, j: int)
        requires
            0 <= i <= j < j_end <= nums.len(),
        ensures
            Self::count_ones_after_flip_window(nums, i, j) <= Self::max_ones_over_windows(nums, i, j_end),
        decreases j_end - i,
    {
        if j < j_end - 1 {
            Self::lemma_mow_bound(nums, i, j_end - 1, j);
        }
    }

    proof fn lemma_maw_bound(nums: Seq<i32>, i_end: int, i: int, j: int)
        requires
            0 <= i <= j < nums.len(),
            i < i_end <= nums.len(),
        ensures
            Self::count_ones_after_flip_window(nums, i, j) <= Self::max_ones_all_windows(nums, i_end),
        decreases i_end,
    {
        if i == i_end - 1 {
            Self::lemma_mow_bound(nums, i, nums.len() as int, j);
        } else {
            Self::lemma_maw_bound(nums, i_end - 1, i, j);
        }
    }

    proof fn lemma_mow_achieved(nums: Seq<i32>, i: int, j_end: int) -> (j: int)
        requires
            0 <= i < j_end <= nums.len(),
        ensures
            i <= j < j_end,
            Self::count_ones_after_flip_window(nums, i, j) == Self::max_ones_over_windows(nums, i, j_end),
        decreases j_end - i,
    {
        if i == j_end - 1 {
            Self::lemma_count_nonneg(nums, i, j_end - 1, nums.len() as int);
            assert(Self::max_ones_over_windows(nums, i, j_end - 1) == 0);
            j_end - 1
        } else {
            let current = Self::count_ones_after_flip_window(nums, i, j_end - 1);
            let rest = Self::max_ones_over_windows(nums, i, j_end - 1);
            if current > rest {
                j_end - 1
            } else {
                Self::lemma_mow_achieved(nums, i, j_end - 1)
            }
        }
    }

    proof fn lemma_maw_achieved(nums: Seq<i32>, i_end: int) -> (pair: (int, int))
        requires
            0 < i_end <= nums.len(),
            nums.len() >= 1,
        ensures
            0 <= pair.0 <= pair.1 < nums.len(),
            Self::count_ones_after_flip_window(nums, pair.0, pair.1) == Self::max_ones_all_windows(nums, i_end),
        decreases i_end,
    {
        let current_row = Self::max_ones_over_windows(nums, i_end - 1, nums.len() as int);
        let rest = Self::max_ones_all_windows(nums, i_end - 1);
        if i_end == 1 || current_row > rest {
            let j = Self::lemma_mow_achieved(nums, i_end - 1, nums.len() as int);
            Self::lemma_count_nonneg(nums, i_end - 1, j, nums.len() as int);
            (i_end - 1, j)
        } else {
            Self::lemma_maw_achieved(nums, i_end - 1)
        }
    }

    pub fn max_ones_after_flip(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 100,
            forall |k: int| 0 <= k < a.len() ==> (#[trigger] a[k] == 0 || a[k] == 1),
        ensures
            result == Self::max_ones_after_one_flip(a@),
            forall |i: int, j: int| 0 <= i <= j < a.len() ==>
                Self::count_ones_after_flip_window(a@, i, j) <= result,
            exists |i: int, j: int| 0 <= i <= j < a.len() &&
                Self::count_ones_after_flip_window(a@, i, j) == result,
    {
        let n = a.len();
        let mut result = 0;
        let mut i = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                1 <= n <= 100,
                forall |idx: int| 0 <= idx < n as int ==> (#[trigger] a[idx] == 0 || a[idx] == 1),
                result as int == Self::max_ones_all_windows(a@, i as int),
                0 <= result <= n as i32,
            decreases n - i,
        {
            let mut j = i;
            while j < n
                invariant
                    0 <= i < n,
                    i <= j <= n,
                    n == a.len(),
                    1 <= n <= 100,
                    forall |idx: int| 0 <= idx < n as int ==> (#[trigger] a[idx] == 0 || a[idx] == 1),
                    result as int == if Self::max_ones_all_windows(a@, i as int) > Self::max_ones_over_windows(a@, i as int, j as int) {
                        Self::max_ones_all_windows(a@, i as int)
                    } else {
                        Self::max_ones_over_windows(a@, i as int, j as int)
                    },
                    0 <= result <= n as i32,
                decreases n - j,
            {
                let mut count = 0;
                let mut k = 0;
                while k < n
                    invariant
                        0 <= k <= n,
                        n == a.len(),
                        0 <= i <= j < n,
                        1 <= n <= 100,
                        forall |idx: int| 0 <= idx < n as int ==> (#[trigger] a[idx] == 0 || a[idx] == 1),
                        0 <= count <= k as i32,
                        count as int == Self::count_ones_after_flip(a@, i as int, j as int, k as int),
                    decreases n - k,
                {
                    let val = if i <= k && k <= j {
                        1 - a[k]
                    } else {
                        a[k]
                    };
                    if val == 1 {
                        count = count + 1;
                    }
                    k = k + 1;
                }
                if count > result {
                    result = count;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        proof {
            assert forall |ii: int, jj: int| 0 <= ii <= jj < a@.len() implies
                Self::count_ones_after_flip_window(a@, ii, jj) <= result as int
            by {
                Self::lemma_maw_bound(a@, n as int, ii, jj);
            };
            let pair = Self::lemma_maw_achieved(a@, n as int);
        }
        result
    }
}

}

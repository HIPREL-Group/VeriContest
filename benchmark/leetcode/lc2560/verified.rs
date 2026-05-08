use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pickable(nums: Seq<i32>, cap: int, i: int) -> int {
        if nums[i] as int <= cap { 1 } else { 0 }
    }

    pub open spec fn max_pick_prefix(nums: Seq<i32>, cap: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n == 1 {
            Self::pickable(nums, cap, 0)
        } else {
            let skip = Self::max_pick_prefix(nums, cap, n - 1);
            let take = Self::max_pick_prefix(nums, cap, n - 2) + Self::pickable(nums, cap, n - 1);
            if take > skip { take } else { skip }
        }
    }

    pub open spec fn feasible_cap(nums: Seq<i32>, cap: int, k: int) -> bool {
        Self::max_pick_prefix(nums, cap, nums.len() as int) >= k
    }

    pub open spec fn max_elem_prefix(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            nums[0] as int
        } else {
            let p = Self::max_elem_prefix(nums, n - 1);
            let c = nums[n - 1] as int;
            if p >= c { p } else { c }
        }
    }

    pub open spec fn max_elem(nums: Seq<i32>) -> int {
        Self::max_elem_prefix(nums, nums.len() as int)
    }

    proof fn lemma_pickable_monotonic(nums: Seq<i32>, x1: int, x2: int, i: int)
        requires
            0 <= i < nums.len(),
            x1 <= x2,
        ensures
            Self::pickable(nums, x1, i) <= Self::pickable(nums, x2, i),
    {
        if nums[i] as int <= x1 {
            assert(nums[i] as int <= x2);
        }
    }

    proof fn lemma_max_pick_prefix_monotonic(nums: Seq<i32>, x1: int, x2: int, n: int)
        requires
            0 <= n <= nums.len(),
            x1 <= x2,
        ensures
            Self::max_pick_prefix(nums, x1, n) <= Self::max_pick_prefix(nums, x2, n),
        decreases n,
    {
        if n > 0 {
            if n == 1 {
                Self::lemma_pickable_monotonic(nums, x1, x2, 0);
            } else {
                Self::lemma_max_pick_prefix_monotonic(nums, x1, x2, n - 1);
                Self::lemma_max_pick_prefix_monotonic(nums, x1, x2, n - 2);
                Self::lemma_pickable_monotonic(nums, x1, x2, n - 1);
            }
        }
    }

    proof fn lemma_feasible_monotonic(nums: Seq<i32>, x1: int, x2: int, k: int)
        requires
            x1 <= x2,
            Self::feasible_cap(nums, x1, k),
        ensures
            Self::feasible_cap(nums, x2, k),
    {
        Self::lemma_max_pick_prefix_monotonic(nums, x1, x2, nums.len() as int);
    }

    proof fn lemma_max_elem_prefix_upper(nums: Seq<i32>, n: int, i: int)
        requires
            1 <= n <= nums.len(),
            0 <= i < n,
        ensures
            nums[i] as int <= Self::max_elem_prefix(nums, n),
        decreases n,
    {
        if n > 1 {
            if i < n - 1 {
                Self::lemma_max_elem_prefix_upper(nums, n - 1, i);
            }
        }
    }

    proof fn lemma_max_pick_all_eligible_lower(nums: Seq<i32>, cap: int, n: int)
        requires
            0 <= n <= nums.len(),
            forall |i: int| 0 <= i < n ==> nums[i] as int <= cap,
        ensures
            Self::max_pick_prefix(nums, cap, n) >= (n + 1) / 2,
        decreases n,
    {
        if n > 0 {
            if n == 1 {
                assert(Self::pickable(nums, cap, 0) == 1);
            } else {
                Self::lemma_max_pick_all_eligible_lower(nums, cap, n - 2);
                assert(nums[n - 1] as int <= cap);
                assert(Self::pickable(nums, cap, n - 1) == 1);
                assert(Self::max_pick_prefix(nums, cap, n)
                    >= Self::max_pick_prefix(nums, cap, n - 2) + 1);
                assert((n - 2 + 1) / 2 + 1 >= (n + 1) / 2) by (nonlinear_arith) {
                }
            }
        }
    }

    proof fn lemma_feasible_at_max(nums: Seq<i32>, k: int)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
            1 <= k <= (nums.len() + 1) / 2,
        ensures
            Self::feasible_cap(nums, Self::max_elem(nums), k),
    {
        assert forall |i: int| 0 <= i < nums.len() implies nums[i] as int <= Self::max_elem(nums) by {
            Self::lemma_max_elem_prefix_upper(nums, nums.len() as int, i);
        }
        Self::lemma_max_pick_all_eligible_lower(nums, Self::max_elem(nums), nums.len() as int);
        assert(Self::max_pick_prefix(nums, Self::max_elem(nums), nums.len() as int) >= (nums.len() + 1) / 2);
        assert((nums.len() + 1) / 2 >= k);
    }

    fn max_elem_exec(nums: &Vec<i32>) -> (m: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            m as int == Self::max_elem(nums@),
    {
        let mut m = nums[0];
        let mut i: usize = 1;
        while i < nums.len()
            invariant
                1 <= i <= nums.len(),
                1 <= nums.len() <= 100000,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000000000,
                m as int == Self::max_elem_prefix(nums@, i as int),
            decreases nums.len() - i,
        {
            if nums[i] > m {
                m = nums[i];
            }
            i = i + 1;
        }
        m
    }

    fn count_with_cap(nums: &Vec<i32>, cap: i32) -> (count: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
            0 <= cap,
        ensures
            count as int == Self::max_pick_prefix(nums@, cap as int, nums.len() as int),
    {
        let mut prev2: i32 = 0;
        let mut prev1: i32 = if nums[0] <= cap { 1 } else { 0 };
        let mut i: usize = 1;
        while i < nums.len()
            invariant
                1 <= i <= nums.len(),
                0 <= cap,
                1 <= nums.len() <= 100000,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000000000,
                prev2 as int == Self::max_pick_prefix(nums@, cap as int, i as int - 1),
                prev1 as int == Self::max_pick_prefix(nums@, cap as int, i as int),
                0 <= prev2 <= i as i32,
                0 <= prev1 <= i as i32,
            decreases nums.len() - i,
        {
            let can_take: i32 = if nums[i] <= cap { 1 } else { 0 };
            let take = prev2 + can_take;
            let curr = if take > prev1 { take } else { prev1 };
            prev2 = prev1;
            prev1 = curr;
            i = i + 1;
        }
        prev1
    }

    fn can_rob(nums: &Vec<i32>, cap: i32, k: i32) -> (ok: bool)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
            0 <= cap,
            1 <= k <= (nums.len() as int + 1) / 2,
        ensures
            ok == Self::feasible_cap(nums@, cap as int, k as int),
    {
        Self::count_with_cap(nums, cap) >= k
    }

    pub fn min_capability(nums: Vec<i32>, k: i32) -> (ans: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
            1 <= k <= (nums.len() as int + 1) / 2,
        ensures
            1 <= ans <= Self::max_elem(nums@),
            Self::feasible_cap(nums@, ans as int, k as int),
            forall |x: int| 1 <= x < ans ==> !#[trigger] Self::feasible_cap(nums@, x, k as int),
    {
        let mut left: i32 = 1;
        let mut right: i32 = Self::max_elem_exec(&nums);
        proof {
            Self::lemma_feasible_at_max(nums@, k as int);
        }
        while left < right
            invariant
                1 <= left <= right <= Self::max_elem(nums@),
                Self::feasible_cap(nums@, right as int, k as int),
                forall |x: int| 1 <= x < left ==> !#[trigger] Self::feasible_cap(nums@, x, k as int),
                1 <= nums.len() <= 100000,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
                1 <= k <= (nums.len() as int + 1) / 2,
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            if Self::can_rob(&nums, mid, k) {
                right = mid;
            } else {
                proof {
                    assert(!Self::feasible_cap(nums@, mid as int, k as int));
                    assert forall |x: int| 1 <= x < mid + 1 implies !Self::feasible_cap(nums@, x, k as int) by {
                        if x < left {
                        } else {
                            assert(left <= x <= mid);
                            if Self::feasible_cap(nums@, x, k as int) {
                                Self::lemma_feasible_monotonic(nums@, x, mid as int, k as int);
                                assert(Self::feasible_cap(nums@, mid as int, k as int));
                            }
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

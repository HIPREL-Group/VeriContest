use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::prefix_sum(nums, n - 1) + nums[n - 1] as int
        }
    }

    pub open spec fn feasible_cap(nums: Seq<i32>, x: int) -> bool {
        forall |n: int| 1 <= n <= nums.len() ==> #[trigger] Self::prefix_sum(nums, n) <= x * n
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

    proof fn lemma_prefix_sum_nonneg(nums: Seq<i32>, n: int)
        requires
            0 <= n <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
        ensures
            0 <= Self::prefix_sum(nums, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_prefix_sum_nonneg(nums, n - 1);
        }
    }

    proof fn lemma_feasible_monotonic(nums: Seq<i32>, x1: int, x2: int)
        requires
            0 <= x1 <= x2,
            Self::feasible_cap(nums, x1),
        ensures
            Self::feasible_cap(nums, x2),
    {
        assert forall |n: int| 1 <= n <= nums.len() implies Self::prefix_sum(nums, n) <= x2 * n by {
            assert(Self::prefix_sum(nums, n) <= x1 * n);
            assert(x1 * n <= x2 * n) by (nonlinear_arith)
                requires 0 <= x1 <= x2, 1 <= n
            {
            }
        }
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

    proof fn lemma_feasible_at_max(nums: Seq<i32>)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
        ensures
            Self::feasible_cap(nums, Self::max_elem(nums)),
    {
        assert forall |j: int| 0 <= j < nums.len() implies nums[j] as int <= Self::max_elem(nums) by {
            Self::lemma_max_elem_prefix_upper(nums, nums.len() as int, j);
        }
        assert forall |n: int| 1 <= n <= nums.len() implies Self::prefix_sum(nums, n) <= Self::max_elem(nums) * n by {
            Self::lemma_prefix_sum_bounded(nums, n, Self::max_elem(nums));
        }
    }

    proof fn lemma_prefix_sum_bounded(nums: Seq<i32>, n: int, b: int)
        requires
            0 <= n <= nums.len(),
            0 <= b,
            forall |i: int| 0 <= i < n ==> nums[i] as int <= b,
        ensures
            Self::prefix_sum(nums, n) <= b * n,
        decreases n,
    {
        if n > 0 {
            assert forall |i: int| 0 <= i < n - 1 implies nums[i] as int <= b by {
            }
            Self::lemma_prefix_sum_bounded(nums, n - 1, b);
            assert(Self::prefix_sum(nums, n) == Self::prefix_sum(nums, n - 1) + nums[n - 1] as int);
            assert(Self::prefix_sum(nums, n - 1) <= b * (n - 1));
            assert(nums[n - 1] as int <= b);
            assert(Self::prefix_sum(nums, n) <= b * n) by (nonlinear_arith)
                requires
                    Self::prefix_sum(nums, n - 1) <= b * (n - 1),
                    nums[n - 1] as int <= b
            {
            }
        }
    }

    fn max_elem_exec(nums: &Vec<i32>) -> (m: i32)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
        ensures
            m as int == Self::max_elem(nums@),
    {
        let mut m = nums[0];
        let mut i: usize = 1;
        while i < nums.len()
            invariant
                1 <= i <= nums.len(),
                2 <= nums.len() <= 100000,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1000000000,
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

    fn can_make(nums: &Vec<i32>, x: i32) -> (ok: bool)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
            0 <= x,
        ensures
            ok == Self::feasible_cap(nums@, x as int),
    {
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                0 <= x,
                2 <= nums.len() <= 100000,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1000000000,
                s as int == Self::prefix_sum(nums@, i as int),
                0 <= s as int <= i as int * 1000000000,
                forall |k: int| 1 <= k <= i as int ==> #[trigger] Self::prefix_sum(nums@, k) <= x as int * k,
            decreases nums.len() - i,
        {
            proof {
                Self::lemma_prefix_sum_nonneg(nums@, i as int);
                assert(i as int * 1000000000 <= 100000 * 1000000000) by (nonlinear_arith)
                    requires i <= nums.len(), nums.len() <= 100000
                {
                }
                assert(0 <= s as int + nums[i as int] as int <= (i as int + 1) * 1000000000) by (nonlinear_arith)
                    requires
                        0 <= s as int <= i as int * 1000000000,
                        0 <= nums[i as int] as int <= 1000000000,
                {
                }
            }
            s = s + nums[i] as i64;
            let denom = i as i64 + 1;
            if (s + denom - 1) / denom > x as i64 {
                proof {
                    assert(denom == (i + 1) as i64);
                    assert(1 <= denom);
                    assert(s > x as i64 * denom) by (nonlinear_arith)
                        requires
                            ((s as int) + (denom as int) - 1) / (denom as int) > x as int,
                            1 <= denom as int,
                            0 <= s as int,
                    {
                    }
                    assert(Self::prefix_sum(nums@, (i + 1) as int) > x as int * ((i + 1) as int));
                }
                return false;
            }
            proof {
                assert(((s as int) + (denom as int) - 1) / (denom as int) <= x as int);
                assert(s <= x as i64 * denom) by (nonlinear_arith)
                    requires
                        ((s as int) + (denom as int) - 1) / (denom as int) <= x as int,
                        1 <= denom as int,
                        0 <= s as int,
                {
                }
                assert(Self::prefix_sum(nums@, (i + 1) as int) <= x as int * ((i + 1) as int));
            }
            i = i + 1;
        }
        true
    }

    pub fn minimize_array_value(nums: Vec<i32>) -> (ans: i32)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
        ensures
            0 <= ans <= Self::max_elem(nums@),
            Self::feasible_cap(nums@, ans as int),
            forall |x: int| 0 <= x < ans ==> !#[trigger] Self::feasible_cap(nums@, x),
    {
        let mut left: i32 = 0;
        let mut right: i32 = Self::max_elem_exec(&nums);
        proof {
            Self::lemma_feasible_at_max(nums@);
        }
        while left < right
            invariant
                0 <= left <= right <= Self::max_elem(nums@),
                Self::feasible_cap(nums@, right as int),
                forall |x: int| 0 <= x < left ==> !#[trigger] Self::feasible_cap(nums@, x),
                2 <= nums.len() <= 100000,
                forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            if Self::can_make(&nums, mid) {
                right = mid;
            } else {
                proof {
                    assert(!Self::feasible_cap(nums@, mid as int));
                    assert forall |x: int| 0 <= x < mid + 1 implies !Self::feasible_cap(nums@, x) by {
                        if x < left {
                        } else {
                            assert(left <= x <= mid);
                            if Self::feasible_cap(nums@, x) {
                                Self::lemma_feasible_monotonic(nums@, x, mid as int);
                                assert(Self::feasible_cap(nums@, mid as int));
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

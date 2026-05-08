use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_prefix_sum(nums: Seq<i32>, k: int) -> int
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::spec_prefix_sum(nums, k - 1) + nums[k - 1] as int
        }
    }

    pub open spec fn spec_range_sum(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
    {
        Self::spec_prefix_sum(nums, r) - Self::spec_prefix_sum(nums, l)
    }

    pub open spec fn spec_start(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums.len(),
    {
        if nums[i] as int > i {
            0
        } else {
            i - nums[i] as int
        }
    }

    pub open spec fn spec_total(nums: Seq<i32>, k: int) -> int
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::spec_total(nums, k - 1)
                + Self::spec_range_sum(nums, Self::spec_start(nums, k - 1), k)
        }
    }

    proof fn lemma_prefix_bounds(nums: Seq<i32>, k: int)
        requires
            0 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            0 <= Self::spec_prefix_sum(nums, k) <= 1000 * k,
        decreases k,
    {
        if k <= 0 {
        } else {
            Self::lemma_prefix_bounds(nums, k - 1);
            assert(0 <= nums[k - 1]);
            assert(Self::spec_prefix_sum(nums, k)
                == Self::spec_prefix_sum(nums, k - 1) + nums[k - 1] as int);
            assert(Self::spec_prefix_sum(nums, k) <= 1000 * (k - 1) + 1000);
            assert(1000 * (k - 1) + 1000 == 1000 * k) by (nonlinear_arith);
        }
    }

    proof fn lemma_prefix_monotone(nums: Seq<i32>, a: int, b: int)
        requires
            0 <= a <= b <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            Self::spec_prefix_sum(nums, a) <= Self::spec_prefix_sum(nums, b),
        decreases b - a,
    {
        if b <= a {
        } else {
            Self::lemma_prefix_monotone(nums, a, b - 1);
            assert(Self::spec_prefix_sum(nums, b)
                == Self::spec_prefix_sum(nums, b - 1) + nums[b - 1] as int);
            assert(0 <= nums[b - 1]);
            assert(Self::spec_prefix_sum(nums, b - 1) <= Self::spec_prefix_sum(nums, b));
            assert(Self::spec_prefix_sum(nums, a) <= Self::spec_prefix_sum(nums, b));
        }
    }

    proof fn lemma_total_bounds(nums: Seq<i32>, k: int)
        requires
            0 <= k <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            0 <= Self::spec_total(nums, k) <= 100000 * k,
        decreases k,
    {
        if k <= 0 {
        } else {
            Self::lemma_total_bounds(nums, k - 1);
            let s = Self::spec_start(nums, k - 1);
            if nums[k - 1] as int > k - 1 {
                assert(s == 0);
            } else {
                assert(s == k - 1 - nums[k - 1] as int);
                assert(0 <= nums[k - 1] as int);
                assert(s <= k - 1);
            }
            assert(0 <= s <= k - 1);
            Self::lemma_prefix_bounds(nums, k);
            Self::lemma_prefix_bounds(nums, s);
            Self::lemma_prefix_monotone(nums, s, k);
            assert(0 <= Self::spec_range_sum(nums, s, k));
            assert(Self::spec_range_sum(nums, s, k)
                <= Self::spec_prefix_sum(nums, k));
            assert(Self::spec_prefix_sum(nums, k) <= 1000 * k);
            assert(k <= 100);
            assert(1000 * k <= 100000) by (nonlinear_arith)
                requires
                    0 <= k <= 100,
            ;
            assert(Self::spec_range_sum(nums, s, k) <= 100000);
            assert(Self::spec_total(nums, k)
                == Self::spec_total(nums, k - 1) + Self::spec_range_sum(nums, s, k));
            assert(Self::spec_total(nums, k) <= 100000 * (k - 1) + 100000);
            assert(100000 * (k - 1) + 100000 == 100000 * k) by (nonlinear_arith);
        }
    }

    pub fn subarray_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::spec_total(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100,
                0 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                prefix@.len() == i + 1,
                forall |j: int| 0 <= j <= i as int ==> #[trigger] prefix@[j] == Self::spec_prefix_sum(nums@, j),
            decreases n - i,
        {
            proof {
                Self::lemma_prefix_bounds(nums@, i as int);
                assert(prefix@[i as int] <= 1000 * i as int);
                assert(1000 * i as int <= 100000) by (nonlinear_arith)
                    requires
                        i as int <= 100,
                ;
            }
            let next = prefix[i] + nums[i];
            prefix.push(next);
            proof {
                assert(next as int == prefix@[i as int] + nums[i as int] as int);
                assert(Self::spec_prefix_sum(nums@, i as int + 1)
                    == Self::spec_prefix_sum(nums@, i as int) + nums[i as int] as int);
                assert(next as int == Self::spec_prefix_sum(nums@, i as int + 1));
                assert forall |j: int| 0 <= j <= i as int + 1 implies
                    #[trigger] prefix@[j] == Self::spec_prefix_sum(nums@, j) by {
                    if j <= i as int {
                    } else {
                        assert(j == i as int + 1);
                    }
                }
            }
            i += 1;
        }

        let mut total: i32 = 0;
        i = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100,
                0 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                prefix@.len() == n + 1,
                forall |j: int| 0 <= j <= n as int ==> #[trigger] prefix@[j] == Self::spec_prefix_sum(nums@, j),
                total as int == Self::spec_total(nums@, i as int),
            decreases n - i,
        {
            let step: usize = nums[i] as usize;
            let mut l: usize = 0;
            if step <= i {
                l = i - step;
            }
            proof {
                assert(step as int == nums[i as int] as int);
                if step <= i {
                    assert(nums[i as int] as int <= i as int);
                    assert(l as int == i as int - step as int);
                    assert(Self::spec_start(nums@, i as int) == l as int);
                } else {
                    assert(nums[i as int] as int > i as int);
                    assert(l == 0);
                    assert(Self::spec_start(nums@, i as int) == 0);
                }
                assert(0 <= l as int <= i as int);
                Self::lemma_prefix_bounds(nums@, i as int + 1);
                Self::lemma_prefix_bounds(nums@, l as int);
                Self::lemma_prefix_monotone(nums@, l as int, i as int + 1);
                assert(0 <= prefix@[i as int + 1] - prefix@[l as int]);
                assert(prefix@[i as int + 1] <= 100000);
                assert(prefix@[i as int + 1] - prefix@[l as int] <= 100000);
                Self::lemma_total_bounds(nums@, i as int);
                assert(0 <= total as int <= 100000 * i as int);
                assert(100000 * i as int <= 10000000) by (nonlinear_arith)
                    requires
                        i as int <= 100,
                ;
                assert(total as int + (prefix@[i as int + 1] - prefix@[l as int]) <= 10100000);
                assert(-2147483648 <= total as int + (prefix@[i as int + 1] - prefix@[l as int]) <= 2147483647);
            }
            let ghost old_total = total;
            let delta = prefix[i + 1] - prefix[l];
            proof {
                assert(delta as int == prefix@[i as int + 1] - prefix@[l as int]);
                assert(delta as int == Self::spec_range_sum(nums@, l as int, i as int + 1));
                assert(delta as int
                    == Self::spec_range_sum(nums@, Self::spec_start(nums@, i as int), i as int + 1));
            }
            total += delta;
            proof {
                assert(total as int == old_total as int + delta as int);
                assert(old_total as int == Self::spec_total(nums@, i as int));
                assert(Self::spec_total(nums@, i as int + 1)
                    == Self::spec_total(nums@, i as int)
                        + Self::spec_range_sum(nums@, Self::spec_start(nums@, i as int), i as int + 1));
                assert(total as int == Self::spec_total(nums@, i as int + 1));
                Self::lemma_total_bounds(nums@, i as int + 1);
            }
            i += 1;
        }

        total
    }
}

}

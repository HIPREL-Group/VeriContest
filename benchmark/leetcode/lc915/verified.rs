use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_partition(nums: Seq<i32>, k: int) -> bool {
        1 <= k < nums.len()
        && (forall |a: int, b: int| #![trigger nums[a], nums[b]]
            0 <= a < k && k <= b < nums.len() ==> nums[a] <= nums[b])
    }

    pub open spec fn prefix_max_spec(nums: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            nums[0] as int
        } else {
            let prev = Self::prefix_max_spec(nums, i - 1);
            if prev > nums[i] as int { prev } else { nums[i] as int }
        }
    }

    pub open spec fn suffix_min_spec(nums: Seq<i32>, i: int) -> int
        decreases nums.len() - i,
    {
        if i >= nums.len() - 1 {
            nums[nums.len() - 1] as int
        } else {
            let next = Self::suffix_min_spec(nums, i + 1);
            if next < nums[i] as int { next } else { nums[i] as int }
        }
    }

    proof fn lemma_prefix_max_upper_bound(nums: Seq<i32>, i: int)
        requires
            nums.len() > 0,
            0 <= i < nums.len(),
        ensures
            forall |j: int| 0 <= j <= i ==> nums[j] as int <= Self::prefix_max_spec(nums, i),
        decreases i,
    {
        if i > 0 {
            Self::lemma_prefix_max_upper_bound(nums, i - 1);
            assert forall |j: int| 0 <= j <= i implies nums[j] as int <= Self::prefix_max_spec(nums, i) by {
                if j < i {
                    assert(nums[j] as int <= Self::prefix_max_spec(nums, i - 1));
                }
            };
        }
    }

    proof fn lemma_prefix_max_attained(nums: Seq<i32>, i: int)
        requires
            nums.len() > 0,
            0 <= i < nums.len(),
        ensures
            exists |j: int| 0 <= j <= i && nums[j] as int == Self::prefix_max_spec(nums, i),
        decreases i,
    {
        if i == 0 {
            let j = 0int;
            assert(0 <= j <= i);
            assert(nums[j] as int == Self::prefix_max_spec(nums, i));
            assert(exists |w: int| 0 <= w <= i && nums[w] as int == Self::prefix_max_spec(nums, i));
        } else {
            Self::lemma_prefix_max_attained(nums, i - 1);
            if Self::prefix_max_spec(nums, i - 1) > nums[i] as int {
                let j = choose |j: int| 0 <= j <= i - 1 && nums[j] as int == Self::prefix_max_spec(nums, i - 1);
                assert(0 <= j <= i);
                assert(nums[j] as int == Self::prefix_max_spec(nums, i));
                assert(exists |w: int| 0 <= w <= i && nums[w] as int == Self::prefix_max_spec(nums, i));
            } else {
                assert(Self::prefix_max_spec(nums, i) == nums[i] as int);
                let j = i;
                assert(0 <= j <= i);
                assert(nums[j] as int == Self::prefix_max_spec(nums, i));
                assert(exists |w: int| 0 <= w <= i && nums[w] as int == Self::prefix_max_spec(nums, i));
            }
        }
    }

    proof fn lemma_suffix_min_lower_bound(nums: Seq<i32>, i: int)
        requires
            nums.len() > 0,
            0 <= i < nums.len(),
        ensures
            forall |j: int| i <= j < nums.len() ==> Self::suffix_min_spec(nums, i) <= nums[j] as int,
        decreases nums.len() - i,
    {
        if i < nums.len() - 1 {
            Self::lemma_suffix_min_lower_bound(nums, i + 1);
            assert forall |j: int| i <= j < nums.len() implies Self::suffix_min_spec(nums, i) <= nums[j] as int by {
                if j > i {
                    assert(Self::suffix_min_spec(nums, i + 1) <= nums[j] as int);
                }
            };
        }
    }

    proof fn lemma_suffix_min_attained(nums: Seq<i32>, i: int)
        requires
            nums.len() > 0,
            0 <= i < nums.len(),
        ensures
            exists |j: int| i <= j < nums.len() && nums[j] as int == Self::suffix_min_spec(nums, i),
        decreases nums.len() - i,
    {
        if i >= nums.len() - 1 {
            let j = i;
            assert(i <= j < nums.len());
            assert(nums[j] as int == Self::suffix_min_spec(nums, i));
            assert(exists |w: int| i <= w < nums.len() && nums[w] as int == Self::suffix_min_spec(nums, i));
        } else {
            Self::lemma_suffix_min_attained(nums, i + 1);
            if Self::suffix_min_spec(nums, i + 1) < nums[i] as int {
                let j = choose |j: int| i + 1 <= j < nums.len() && nums[j] as int == Self::suffix_min_spec(nums, i + 1);
                assert(i <= j < nums.len());
                assert(nums[j] as int == Self::suffix_min_spec(nums, i));
                assert(exists |w: int| i <= w < nums.len() && nums[w] as int == Self::suffix_min_spec(nums, i));
            } else {
                assert(Self::suffix_min_spec(nums, i) == nums[i] as int);
                let j = i;
                assert(i <= j < nums.len());
                assert(nums[j] as int == Self::suffix_min_spec(nums, i));
                assert(exists |w: int| i <= w < nums.len() && nums[w] as int == Self::suffix_min_spec(nums, i));
            }
        }
    }

    proof fn lemma_boundary_implies_valid_partition(nums: Seq<i32>, k: int)
        requires
            nums.len() > 0,
            1 <= k < nums.len(),
            Self::prefix_max_spec(nums, k - 1) <= Self::suffix_min_spec(nums, k),
        ensures
            Self::valid_partition(nums, k),
    {
        Self::lemma_prefix_max_upper_bound(nums, k - 1);
        Self::lemma_suffix_min_lower_bound(nums, k);
        assert forall |a: int, b: int| #![trigger nums[a], nums[b]]
            0 <= a < k && k <= b < nums.len() implies nums[a] <= nums[b] by {
            assert(nums[a] as int <= Self::prefix_max_spec(nums, k - 1));
            assert(Self::suffix_min_spec(nums, k) <= nums[b] as int);
        };
    }

    proof fn lemma_valid_partition_implies_boundary(nums: Seq<i32>, k: int)
        requires
            nums.len() > 0,
            1 <= k < nums.len(),
            Self::valid_partition(nums, k),
        ensures
            Self::prefix_max_spec(nums, k - 1) <= Self::suffix_min_spec(nums, k),
    {
        Self::lemma_prefix_max_attained(nums, k - 1);
        Self::lemma_suffix_min_attained(nums, k);
        let a = choose |a: int| 0 <= a <= k - 1 && nums[a] as int == Self::prefix_max_spec(nums, k - 1);
        let b = choose |b: int| k <= b < nums.len() && nums[b] as int == Self::suffix_min_spec(nums, k);
        assert(0 <= a < k);
        assert(k <= b < nums.len());
        assert(nums[a] <= nums[b]);
    }

    proof fn lemma_not_boundary_not_valid(nums: Seq<i32>, k: int)
        requires
            nums.len() > 0,
            1 <= k < nums.len(),
            !(Self::prefix_max_spec(nums, k - 1) <= Self::suffix_min_spec(nums, k)),
        ensures
            !Self::valid_partition(nums, k),
    {
        if Self::valid_partition(nums, k) {
            Self::lemma_valid_partition_implies_boundary(nums, k);
            assert(false);
        }
    }

    pub fn partition_disjoint(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            exists |k: int| Self::valid_partition(nums@, k),
        ensures
            1 <= result as int,
            (result as int) < nums.len() as int,
            Self::valid_partition(nums@, result as int),
            forall |k: int| 1 <= k && k < result as int ==> !Self::valid_partition(nums@, k),
    {
        let n = nums.len();
        let mut suffix_min: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                0 <= i <= n,
                suffix_min.len() == i,
                forall |j: int| 0 <= j < i as int ==> suffix_min[j] == nums[j],
            decreases n - i,
        {
            suffix_min.push(nums[i]);
            i += 1;
        }

        let mut i: usize = n - 1;
        while i > 0
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                0 <= i < n,
                suffix_min.len() == n,
                forall |j: int| i as int <= j < n as int ==> suffix_min[j] as int == Self::suffix_min_spec(nums@, j),
                forall |j: int| 0 <= j < i as int ==> suffix_min[j] == nums[j],
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] nums@[j] <= 1_000_000,
            decreases i,
        {
            i -= 1;
            if suffix_min[i + 1] < suffix_min[i] {
                suffix_min.set(i, suffix_min[i + 1]);
            }
        }

        let mut prefix_max = nums[0];
        let mut i: usize = 0;
        while i < n - 1
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                0 <= i <= n - 1,
                suffix_min.len() == n,
                forall |j: int| 0 <= j < n as int ==> suffix_min[j] as int == Self::suffix_min_spec(nums@, j),
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] nums@[j] <= 1_000_000,
                i == 0 ==> prefix_max as int == nums@[0] as int,
                i > 0 ==> prefix_max as int == Self::prefix_max_spec(nums@, i as int - 1),
                0 <= prefix_max <= 1_000_000,
                forall |k: int| 1 <= k <= i as int ==> !Self::valid_partition(nums@, k),
            decreases n - 1 - i,
        {
            if nums[i] > prefix_max {
                prefix_max = nums[i];
            }
            proof {
                if i == 0 {
                    assert(prefix_max as int == Self::prefix_max_spec(nums@, 0));
                } else {
                    assert(prefix_max as int == Self::prefix_max_spec(nums@, i as int));
                }
            }

            if prefix_max <= suffix_min[i + 1] {
                proof {
                    Self::lemma_boundary_implies_valid_partition(nums@, i as int + 1);
                    assert forall |k: int| 1 <= k && k < i as int + 1 implies !Self::valid_partition(nums@, k) by {
                        assert(k <= i as int);
                    };
                }
                return i as i32 + 1;
            }

            proof {
                Self::lemma_not_boundary_not_valid(nums@, i as int + 1);
                assert forall |k: int| 1 <= k && k <= i as int + 1 implies !Self::valid_partition(nums@, k) by {
                    if k <= i as int {
                    } else {
                        assert(k == i as int + 1);
                    }
                };
            }
            i += 1;
        }

        proof {
            let k = choose |k: int| Self::valid_partition(nums@, k);
            assert(1 <= k < nums.len());
            assert(k <= i as int);
            assert(!Self::valid_partition(nums@, k));
            assert(false);
        }
        0
    }
}

}

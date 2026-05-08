use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted_range(nums: &Vec<i32>, start: int, end: int) -> bool {
        forall|i: int, j: int| start <= i <= j < end ==> nums[i] <= nums[j]
    }

    pub open spec fn pivot_ok(nums: &Vec<i32>, p: int) -> bool {
        0 <= p < nums.len() && if p == 0 {
            Self::sorted_range(nums, 0, nums.len() as int)
        } else {
            nums[p - 1] > nums[p] && Self::sorted_range(nums, 0, p)
                && Self::sorted_range(nums, p, nums.len() as int)
                && forall|i: int, j: int|
                    p <= i < nums.len() && 0 <= j < p ==> nums[i] <= nums[j]
        }
    }

    pub open spec fn rotated_sorted(nums: &Vec<i32>) -> bool {
        exists|p: int| #[trigger] Self::pivot_ok(nums, p)
    }

    fn lower_bound(nums: &Vec<i32>, start: usize, end: usize, target: i32) -> (pos: usize)
        requires
            start <= end <= nums.len(),
            Self::sorted_range(nums, start as int, end as int),
        ensures
            start <= pos <= end,
            forall|i: int| start as int <= i < pos as int ==> nums[i] < target,
            forall|i: int| pos as int <= i < end as int ==> nums[i] >= target,
    {
        let mut lo = start;
        let mut hi = end;

        while lo < hi
            invariant
                start <= lo <= hi <= end <= nums.len(),
                Self::sorted_range(nums, start as int, end as int),
                forall|i: int| start as int <= i < lo as int ==> nums[i] < target,
                forall|i: int| hi as int <= i < end as int ==> nums[i] >= target,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            if nums[mid] < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        lo
    }

    fn search_sorted_range(nums: &Vec<i32>, start: usize, end: usize, target: i32) -> (found: bool)
        requires
            start <= end <= nums.len(),
            Self::sorted_range(nums, start as int, end as int),
        ensures
            found == (exists|i: int| start as int <= i < end as int && nums[i] == target),
    {
        let pos = Self::lower_bound(nums, start, end, target);
        let found = pos < end && nums[pos] == target;

        proof {
            if found {
                assert(start <= pos);
                assert(pos < end);
                assert(nums[pos as int] == target);
                assert(exists|i: int| start as int <= i < end as int && nums[i] == target);
            } else {
                assert forall|i: int| start as int <= i < end as int implies nums[i] != target by {
                    if i < pos as int {
                        assert(nums[i] < target);
                    } else {
                        assert(pos as int <= i);
                        assert(i < end as int);
                        assert(nums[i] >= target);
                        if pos < end {
                            assert(nums[pos as int] >= target);
                            assert(nums[pos as int] != target);
                            assert(nums[pos as int] > target);
                            assert(nums[i] >= nums[pos as int]);
                            assert(nums[i] > target);
                        }
                    }
                }
                assert(!(exists|i: int| start as int <= i < end as int && nums[i] == target));
            }
        }

        found
    }

    pub fn search(nums: Vec<i32>, target: i32) -> (result: bool)
        requires
            1 <= nums.len() <= 5_000,
            forall|i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            Self::rotated_sorted(&nums),
            -10_000 <= target <= 10_000,
        ensures
            result == (exists|i: int| 0 <= i < nums.len() && nums[i] == target),
    {
        let ghost p: int = choose|pivot: int| Self::pivot_ok(&nums, pivot);

        let n = nums.len();
        let mut i: usize = 1;

        while i < n && nums[i - 1] <= nums[i]
            invariant
                1 <= nums.len() <= 5_000,
                n == nums.len(),
                1 <= i <= n,
                forall|k: int| 0 <= k < nums.len() ==> -10_000 <= #[trigger] nums[k] <= 10_000,
                Self::rotated_sorted(&nums),
                0 <= p < nums.len(),
                Self::pivot_ok(&nums, p),
                forall|j: int| 1 <= j < i as int ==> #[trigger] nums[j - 1] <= nums[j],
                p > 0 ==> i as int <= p,
            decreases n - i,
        {
            i += 1;
        }

        proof {
            if p == 0 {
                if i < n {
                    assert(nums[i as int - 1] <= nums[i as int]);
                    assert(false);
                }
                assert(i == n);
            } else {
                if (i as int) < p {
                    assert(nums[i as int - 1] <= nums[i as int]);
                    assert(false);
                }
                assert((i as int) == p);
            }
        }

        let pivot = if i < n { i } else { 0usize };

        proof {
            assert(pivot as int == p);
        }

        let found_suffix = Self::search_sorted_range(&nums, pivot, n, target);
        let found_prefix = Self::search_sorted_range(&nums, 0, pivot, target);
        let result = found_suffix || found_prefix;

        proof {
            if result {
                if found_suffix {
                    assert(exists|j: int| pivot as int <= j < n as int && nums[j] == target);
                    assert(exists|j: int| 0 <= j < nums.len() && nums[j] == target);
                } else {
                    assert(found_prefix);
                    assert(exists|j: int| 0 <= j < pivot as int && nums[j] == target);
                    assert(exists|j: int| 0 <= j < nums.len() && nums[j] == target);
                }
            } else {
                assert(!(exists|j: int| 0 <= j < nums.len() && nums[j] == target)) by {
                    assert(!(exists|j: int| pivot as int <= j < n as int && nums[j] == target));
                    assert(!(exists|j: int| 0 <= j < pivot as int && nums[j] == target));
                    if exists|j: int| 0 <= j < nums.len() && nums[j] == target {
                        let j = choose|j: int| 0 <= j < nums.len() && nums[j] == target;
                        if j < pivot as int {
                            assert(false);
                        } else {
                            assert(false);
                        }
                    }
                }
            }
        }

        result
    }
}

}

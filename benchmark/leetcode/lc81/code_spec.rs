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

        while lo < hi {
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
        let n = nums.len();
        let mut i: usize = 1;

        while i < n && nums[i - 1] <= nums[i] {
            i += 1;
        }

        let pivot = if i < n { i } else { 0usize };
        let found_suffix = Self::search_sorted_range(&nums, pivot, n, target);
        let found_prefix = Self::search_sorted_range(&nums, 0, pivot, target);
        let result = found_suffix || found_prefix;
        result
    }
}

}

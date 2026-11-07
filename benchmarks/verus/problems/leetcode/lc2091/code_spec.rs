use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_min_at(nums: Seq<i32>, idx: int) -> bool {
        0 <= idx < nums.len()
        && forall |j: int| 0 <= j < nums.len() ==> nums[idx] <= #[trigger] nums[j]
    }

    pub open spec fn is_max_at(nums: Seq<i32>, idx: int) -> bool {
        0 <= idx < nums.len()
        && forall |j: int| 0 <= j < nums.len() ==> nums[idx] >= #[trigger] nums[j]
    }

    pub fn minimum_deletions(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] != #[trigger] nums[j],
            forall |i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            1 <= result <= nums.len(),
            exists |min_idx: int, max_idx: int|
                0 <= min_idx < nums.len()
                && 0 <= max_idx < nums.len()
                && Self::is_min_at(nums@, min_idx)
                && Self::is_max_at(nums@, max_idx)
                && result as int == (if min_idx <= max_idx {
                    {
                        let left = max_idx + 1;
                        let right = nums.len() - min_idx;
                        let both = min_idx + 1 + nums.len() - max_idx;
                        if left <= right && left <= both {
                            left
                        } else if right <= both {
                            right
                        } else {
                            both
                        }
                    }
                } else {
                    {
                        let left = min_idx + 1;
                        let right = nums.len() - max_idx;
                        let both = max_idx + 1 + nums.len() - min_idx;
                        if left <= right && left <= both {
                            left
                        } else if right <= both {
                            right
                        } else {
                            both
                        }
                    }
                }),
    {
        let n = nums.len();
        let mut min_idx: usize = 0;
        let mut max_idx: usize = 0;
        let mut i: usize = 1;

        while i < n
        {
            if nums[i] < nums[min_idx] {
                min_idx = i;
            }
            if nums[i] > nums[max_idx] {
                max_idx = i;
            }
            i += 1;
        }

        let small = if min_idx <= max_idx { min_idx } else { max_idx };
        let large = if min_idx <= max_idx { max_idx } else { min_idx };

        let left = large + 1;
        let right = n - small;
        let both = small + 1 + n - large;

        let ans = if left <= right && left <= both {
            left
        } else if right <= both {
            right
        } else {
            both
        };

        ans as i32
    }
}

}

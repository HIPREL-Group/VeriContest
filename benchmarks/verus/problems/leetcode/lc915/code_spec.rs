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
        while i < n {
            suffix_min.push(nums[i]);
            i += 1;
        }

        let mut i: usize = n - 1;
        while i > 0 {
            i -= 1;
            if suffix_min[i + 1] < suffix_min[i] {
                suffix_min.set(i, suffix_min[i + 1]);
            }
        }

        let mut prefix_max = nums[0];
        let mut i: usize = 0;
        while i < n - 1 {
            if nums[i] > prefix_max {
                prefix_max = nums[i];
            }
            if prefix_max <= suffix_min[i + 1] {
                return i as i32 + 1;
            }
            i += 1;
        }

        0
    }
}

}

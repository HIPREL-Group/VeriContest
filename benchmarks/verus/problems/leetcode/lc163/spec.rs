use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_ranges(nums: Seq<i32>, i: int, next: i32, upper: i32) -> Seq<(i32, i32)>
        decreases nums.len() - i
    {
        if i >= nums.len() {
            if next <= upper {
                seq![(next, upper)]
            } else {
                seq![]
            }
        } else {
            let cur = nums[i];
            let next_after: i32 = if cur == i32::MAX { i32::MAX } else { (cur + 1) as i32 };
            if next < cur {
                seq![(next, (cur - 1) as i32)] + Self::suffix_ranges(nums, i + 1, next_after, upper)
            } else {
                Self::suffix_ranges(nums, i + 1, next_after, upper)
            }
        }
    }

    pub open spec fn result_pairs(ranges: Seq<Vec<i32>>) -> Seq<(i32, i32)> {
        Seq::new(
            ranges.len(),
            |j: int| if ranges[j].len() == 2 { (ranges[j][0], ranges[j][1]) } else { (0, 0) },
        )
    }

    pub fn find_missing_ranges(nums: Vec<i32>, lower: i32, upper: i32) -> (result: Vec<Vec<i32>>)
        requires
            0 <= nums.len() <= 100,
            lower <= upper,
            -1000000000 <= lower <= 1000000000,
            -1000000000 <= upper <= 1000000000,
            forall |i: int| 0 <= i < nums.len() ==> lower <= #[trigger] nums[i] <= upper,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
        ensures
            forall |j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            Self::result_pairs(result@) == Self::suffix_ranges(nums@, 0, lower, upper),
    {
    }
}

}

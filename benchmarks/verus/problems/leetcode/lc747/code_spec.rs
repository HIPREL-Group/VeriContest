use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_max_index(nums: Seq<i32>, idx: int) -> bool {
        0 <= idx < nums.len() &&
        forall |j: int| 0 <= j < nums.len() ==> nums[idx] >= #[trigger] nums[j]
    }

    pub open spec fn is_dominant(nums: Seq<i32>, idx: int) -> bool {
        Self::is_max_index(nums, idx) &&
        forall |j: int| 0 <= j < nums.len() && j != idx ==> nums[idx] >= 2 * #[trigger] nums[j]
    }

    pub fn dominant_index(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
            exists |i: int| #![trigger nums[i]] 0 <= i < nums.len() &&
                forall |j: int| 0 <= j < nums.len() && j != i ==> nums[i] > #[trigger] nums[j],
        ensures
            -1 <= result < nums.len() as i32,
            result >= 0 ==> Self::is_dominant(nums@, result as int),
            result < 0 ==> forall |i: int| 0 <= i < nums.len() ==> !Self::is_dominant(nums@, i),
    {
        let n = nums.len();
        let mut max_val: i32 = nums[0];
        let mut max_idx: usize = 0;
        let mut second_max: i32 = -1;

        let mut i: usize = 1;
        while i < n {
            if nums[i] > max_val {
                second_max = max_val;
                max_val = nums[i];
                max_idx = i;
            } else if nums[i] > second_max {
                second_max = nums[i];
            }
            i += 1;
        }

        if max_val >= 2 * second_max {
            max_idx as i32
        } else {
            -1
        }
    }
}

}

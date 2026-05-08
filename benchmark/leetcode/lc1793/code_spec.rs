use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn min_in_range(s: Seq<i32>, i: int, j: int) -> int
        decreases j - i,
    {
        if i >= j {
            s[i] as int
        } else {
            Self::spec_min(s[i] as int, Self::min_in_range(s, i + 1, j))
        }
    }

    pub open spec fn score_spec(s: Seq<i32>, i: int, j: int) -> int {
        Self::min_in_range(s, i, j) * (j - i + 1)
    }

    pub fn maximum_score(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20_000,
            0 <= k < nums.len() as i32,
        ensures
            exists|i: int, j: int|
                0 <= i && i <= k as int && k as int <= j && j < nums@.len() && result as int
                    == Self::score_spec(nums@, i, j),
            forall|i: int, j: int|
                0 <= i && i <= k as int && k as int <= j && j < nums@.len() ==> Self::score_spec(
                    nums@,
                    i,
                    j,
                ) <= result as int,
            result >= 1i32,
    {
        let n = nums.len();
        let k_usize = k as usize;
        let mut left: usize = k_usize;
        let mut right: usize = k_usize;
        let mut cur_min: i32 = nums[k_usize];
        let mut result: i32 = cur_min;

        while left > 0 || right < n - 1 {
            let left_val: i32 = if left > 0 { nums[left - 1] } else { 0 };
            let right_val: i32 = if right < n - 1 { nums[right + 1] } else { 0 };

            if left_val >= right_val {
                left = left - 1;
                if nums[left] < cur_min {
                    cur_min = nums[left];
                }
            } else {
                right = right + 1;
                if nums[right] < cur_min {
                    cur_min = nums[right];
                }
            }

            let score: i32 = cur_min * ((right - left + 1) as i32);

            if score > result {
                result = score;
            }
        }

        result
    }
}

} 

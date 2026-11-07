use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_closest_number(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            exists|idx: int| 0 <= idx < nums.len() && nums[idx] == res,
            forall|i: int|
                0 <= i < nums.len() ==> (if res >= 0 { res as int } else { -(res as int) })
                    <= (if #[trigger] nums[i] >= 0 { nums[i] as int } else { -(nums[i] as int) }),
            forall|i: int|
                0 <= i < nums.len() &&
                (if res >= 0 { res as int } else { -(res as int) })
                    == (if #[trigger] nums[i] >= 0 { nums[i] as int } else { -(nums[i] as int) })
                    ==> nums[i] <= res,
    {
        let n = nums.len();
        let mut best = nums[0];
        let mut i: usize = 1;

        while i < n {
            let current = nums[i];
            let prev_best = best;
            let prev_best_abs = if prev_best < 0 { -prev_best } else { prev_best };
            let current_abs = if current < 0 { -current } else { current };
            let new_best = if current_abs < prev_best_abs || (current_abs == prev_best_abs && current > prev_best) {
                current
            } else {
                prev_best
            };

            best = new_best;
            i += 1;
        }

        best
    }
}

}

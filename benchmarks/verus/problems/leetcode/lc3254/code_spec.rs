use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn consecutive_step(nums: Seq<i32>, i: int) -> bool
        recommends
            0 <= i + 1 < nums.len(),
    {
        nums[i + 1] == nums[i] + 1
    }

    pub open spec fn window_has_power(nums: Seq<i32>, start: int, k: int) -> bool
        recommends
            0 <= start,
            1 <= k,
            start + k <= nums.len(),
    {
        forall |j: int| start <= j < start + k - 1 ==> #[trigger] Self::consecutive_step(nums, j)
    }

    pub open spec fn window_power(nums: Seq<i32>, start: int, k: int) -> int
        recommends
            0 <= start,
            1 <= k,
            start + k <= nums.len(),
    {
        if Self::window_has_power(nums, start, k) {
            nums[start + k - 1] as int
        } else {
            -1
        }
    }

    pub fn results_array(nums: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 500,
            1 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result@.len() == nums.len() as int - k as int + 1,
            forall |i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] as int == Self::window_power(nums@, i, k as int),
    {
        let n = nums.len();
        let k_usize = k as usize;
        let mut result: Vec<i32> = Vec::new();
        let mut run_len: usize = 1;
        if k_usize == 1 {
            result.push(nums[0]);
        }
        let mut i: usize = 1;
        while i < n {
            let prev_val = nums[i - 1];
            let curr_val = nums[i];
            let prev_run_len = run_len;
            if prev_val + 1 == curr_val {
                run_len = prev_run_len + 1;
            } else {
                run_len = 1;
            }
            if i + 1 >= k_usize {
                let out = if run_len >= k_usize { curr_val } else { -1 };
                result.push(out);
            }
            i += 1;
        }
        result
    }
}

}
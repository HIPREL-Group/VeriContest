use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_ok(nums: Seq<i32>, limit: int, l: int, r: int) -> bool {
        &&& 0 <= l < r <= nums.len()
        &&& forall |i: int, j: int| l <= i < r && l <= j < r ==> (nums[i] as int - nums[j] as int) <= limit
    }

    pub fn longest_subarray(nums: Vec<i32>, limit: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            0 <= limit <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= result <= nums.len() as i32,
            exists |l: int, r: int| Self::window_ok(nums@, limit as int, l, r) && result as int == r - l,
            forall |l: int, r: int| Self::window_ok(nums@, limit as int, l, r) ==> r - l <= result as int,
    {
        let n = nums.len();
        let mut max_q: Vec<usize> = Vec::new();
        let mut min_q: Vec<usize> = Vec::new();
        let mut init_i: usize = 0;
        while init_i < n {
            max_q.push(0usize);
            min_q.push(0usize);
            init_i += 1;
        }
        let mut max_head: usize = 0;
        let mut max_tail: usize = 0;
        let mut min_head: usize = 0;
        let mut min_tail: usize = 0;
        let mut left: usize = 0;
        let mut right: usize = 0;
        let mut best: usize = 0;

        while right < n
        {
            let right_num = nums[right];
            while max_head < max_tail && nums[max_q[max_tail - 1]] < right_num
            {
                let last_idx = max_q[max_tail - 1];
                let last_num = nums[last_idx];
                max_tail -= 1;
            }
            max_q.set(max_tail, right);
            max_tail += 1;

            while min_head < min_tail && nums[min_q[min_tail - 1]] > right_num
            {
                let last_idx = min_q[min_tail - 1];
                let last_num = nums[last_idx];
                min_tail -= 1;
            }
            min_q.set(min_tail, right);
            min_tail += 1;

            while nums[max_q[max_head]] - nums[min_q[min_head]] > limit
            {
                if max_q[max_head] == left {
                    max_head += 1;
                }
                if min_q[min_head] == left {
                    min_head += 1;
                }
                left += 1;
            }

            let len = right - left + 1;
            if best < len {
                best = len;
            }
            right += 1;
        }

        best as i32
    }
}

}
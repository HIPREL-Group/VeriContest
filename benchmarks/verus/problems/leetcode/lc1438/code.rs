impl Solution {
    pub fn longest_subarray(nums: Vec<i32>, limit: i32) -> i32
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
            max_q[max_tail] = right;
            max_tail += 1;

            while min_head < min_tail && nums[min_q[min_tail - 1]] > right_num
            {
                let last_idx = min_q[min_tail - 1];
                let last_num = nums[last_idx];
                min_tail -= 1;
            }
            min_q[min_tail] = right;
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

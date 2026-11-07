impl Solution {
    pub fn min_sub_array_len(target: i32, nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut left: usize = 0;
        let mut right: usize = 0;
        let mut window_sum: i64 = 0;
        let mut best: usize = n + 1;

        while right < n
        {
            window_sum = window_sum + nums[right] as i64;
            right = right + 1;

            while window_sum >= target as i64
            {
                let len = right - left;
                if len < best {
                    best = len;
                }
                window_sum = window_sum - nums[left] as i64;
                left = left + 1;
            }
        }

        if best == n + 1 {
            0
        } else {
            best as i32
        }
    }
}

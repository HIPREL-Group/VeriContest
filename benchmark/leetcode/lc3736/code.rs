impl Solution {
    pub fn min_moves(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut max_val = nums[0];
        let mut i = 1usize;
        while i < n {
            let cur = nums[i];
            let old_max = max_val;
            if cur > old_max {
                max_val = cur;
            } else {
                max_val = old_max;
            }
            i = i + 1;
        }
        let mut ans: i64 = 0;
        let mut j = 0usize;
        while j < n {
            let delta = max_val - nums[j];
            ans = ans + delta as i64;
            j = j + 1;
        }
        ans as i32
    }
}

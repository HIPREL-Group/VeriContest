impl Solution {
    pub fn find_target_sum_ways(nums: Vec<i32>, target: i32) -> i32 {
        let n = nums.len();
        let mut total = 0i32;
        let mut i = 0usize;
        while i < n {
            total = total + nums[i];
            i += 1;
        }
        let transformed = total + target;
        if transformed < 0 {
            return 0;
        }
        if transformed % 2 != 0 {
            return 0;
        }
        let goal_i = transformed / 2;
        let goal = goal_i as usize;
        if goal_i > total {
            return 0;
        }
        let goal_len = goal + 1;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < goal_len {
            dp.push(0);
            k += 1;
        }
        dp[0] = 1;
        let mut idx: usize = 0;
        while idx < n {
            let num = nums[idx] as usize;
            let mut s = goal_len;
            while s > 0 {
                let cur = s - 1;
                if num <= cur {
                    let old_value = dp[cur];
                    let add_value = dp[cur - num];
                    dp[cur] = old_value + add_value;
                }
                s = cur;
            }
            idx += 1;
        }
        dp[goal]
    }
}

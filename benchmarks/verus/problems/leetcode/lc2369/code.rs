impl Solution {
    pub fn valid_partition(nums: Vec<i32>) -> bool {
        let n = nums.len() as i32;
        let mut dp: Vec<i32> = Vec::new();
        dp.push(1);
        let mut i: i32 = 1;
        while i <= n {
            let mut cur: i32 = 0;
            if i >= 2 {
                if nums[(i - 2) as usize] == nums[(i - 1) as usize] && dp[(i - 2) as usize] == 1 {
                    cur = 1;
                }
            }
            if i >= 3 {
                if nums[(i - 3) as usize] == nums[(i - 2) as usize] && nums[(i - 2) as usize] == nums[(i - 1) as usize] && dp[(i - 3) as usize] == 1 {
                    cur = 1;
                }
                if nums[(i - 3) as usize] + 1 == nums[(i - 2) as usize] && nums[(i - 2) as usize] + 1 == nums[(i - 1) as usize] && dp[(i - 3) as usize] == 1 {
                    cur = 1;
                }
            }
            dp.push(cur);
            i = i + 1;
        }
        dp[n as usize] == 1
    }
}

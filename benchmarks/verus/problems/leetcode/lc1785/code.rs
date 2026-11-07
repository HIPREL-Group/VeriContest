impl Solution {
    pub fn min_elements(nums: Vec<i32>, limit: i32, goal: i32) -> i32 {
        let n = nums.len();
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + nums[i] as i64;
            i = i + 1;
        }
        let diff: i64 = if sum >= goal as i64 { sum - goal as i64 } else { goal as i64 - sum };
        let result: i64 = (diff + limit as i64 - 1) / limit as i64;
        result as i32
    }
}

impl Solution {
    pub fn left_right_difference(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut total_sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total_sum += nums[i] as i64;
            i += 1;
        }
        let mut answer: Vec<i32> = vec![0i32; n];
        let mut left_sum: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            let right_sum: i64 = total_sum - left_sum - nums[j] as i64;
            let diff: i64 = left_sum - right_sum;
            if diff >= 0 {
                answer[j] = diff as i32;
            } else {
                answer[j] = (-diff) as i32;
            }
            left_sum += nums[j] as i64;
            j += 1;
        }
        answer
    }
}

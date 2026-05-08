impl Solution {
    pub fn get_averages(nums: Vec<i32>, k: i32) -> Vec<i32> {
        let n = nums.len();
        let radius = k as usize;
        let window_len = 2 * radius + 1;
        let mut result: Vec<i32> = Vec::new();

        let mut i: usize = 0;
        while i < n {
            result.push(-1);
            i += 1;
        }

        if window_len > n {
            return result;
        }

        let mut sum: i64 = 0;
        i = 0;
        while i < window_len {
            sum += nums[i] as i64;
            i += 1;
        }

        let denom = window_len as i64;
        let limit = n - radius;
        let mut center = radius;
        while center < limit {
            let avg = (sum / denom) as i32;
            result[center] = avg;
            if center + 1 < limit {
                sum += nums[center + radius + 1] as i64;
                sum -= nums[center - radius] as i64;
            }
            center += 1;
        }

        result
    }
}

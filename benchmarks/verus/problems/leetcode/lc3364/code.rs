impl Solution {
    pub fn minimum_sum_subarray(nums: Vec<i32>, l: i32, r: i32) -> i32 {
        let n = nums.len();
        let mut best: i64 = -1;
        let mut len: usize = l as usize;
        while len <= r as usize {
            let mut start: usize = 0;
            while start + len <= n {
                let mut sum: i64 = 0;
                let mut t: usize = 0;
                while t < len {
                    sum = sum + nums[start + t] as i64;
                    t += 1;
                }
                if sum > 0 && (best == -1 || sum < best) {
                    best = sum;
                }
                start += 1;
            }
            len += 1;
        }
        best as i32
    }
}

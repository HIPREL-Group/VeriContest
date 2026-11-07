impl Solution {
    pub fn count_subarrays(nums: Vec<i32>, k: i64) -> i64 {
        let n = nums.len();
        let mut left = 0usize;
        let mut sum = 0i64;
        let mut answer = 0i64;
        let mut right = 0usize;

        while right < n {
            sum += nums[right] as i64;

            while left <= right && sum * (right - left + 1) as i64 >= k {
                sum -= nums[left] as i64;
                left += 1;
            }

            answer += (right + 1 - left) as i64;
            right += 1;
        }

        answer
    }
}

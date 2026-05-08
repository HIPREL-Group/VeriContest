impl Solution {
    fn can_split(nums: &Vec<i32>, k: i32, max_sum: i64) -> bool {
        let mut count: i32 = 1;
        let mut current_sum: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            if current_sum + nums[i] as i64 > max_sum {
                count += 1;
                current_sum = nums[i] as i64;
            } else {
                current_sum += nums[i] as i64;
            }
            i += 1;
        }
        count <= k
    }

    pub fn split_array(nums: Vec<i32>, k: i32) -> i32 {
        let mut left: i64 = 0;
        let mut right: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] as i64 > left {
                left = nums[i] as i64;
            }
            right += nums[i] as i64;
            i += 1;
        }
        while left < right {
            let mid = left + (right - left) / 2;
            if Self::can_split(&nums, k, mid) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left as i32
    }
}

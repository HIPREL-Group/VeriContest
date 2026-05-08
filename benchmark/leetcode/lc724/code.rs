impl Solution {
    pub fn pivot_index(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + nums[i];
            i = i + 1;
        }
        let mut left_sum: i32 = 0;
        i = 0;
        while i < n {
            if left_sum == total - left_sum - nums[i] {
                return i as i32;
            }
            left_sum = left_sum + nums[i];
            i = i + 1;
        }
        -1
    }
}

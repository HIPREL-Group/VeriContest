impl Solution {
    pub fn min_start_value(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut min_sum: i32 = 0;
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + nums[i];
            if sum < min_sum {
                min_sum = sum;
            }
            i += 1;
        }
        1 - min_sum
    }
}

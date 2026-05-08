impl Solution {
    pub fn sum_of_squares(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if n % (i + 1) == 0 {
                total += nums[i] * nums[i];
            }
            i += 1;
        }
        total
    }
}

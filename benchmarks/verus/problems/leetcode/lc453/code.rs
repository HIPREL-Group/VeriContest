impl Solution {
    pub fn min_moves(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut min_val = nums[0];
        let mut sum = nums[0] as i64;
        let mut i = 1usize;
        while i < n {
            if nums[i] < min_val {
                min_val = nums[i];
            }
            sum = sum + nums[i] as i64;
            i = i + 1;
        }
        (sum - (n as i64) * (min_val as i64)) as i32
    }
}

impl Solution {
    pub fn max_absolute_sum(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut s: i32 = 0;
        let mut max_prefix: i32 = 0;
        let mut min_prefix: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            s = s + nums[i];
            if s > max_prefix {
                max_prefix = s;
            }
            if s < min_prefix {
                min_prefix = s;
            }
            i = i + 1;
        }
        max_prefix - min_prefix
    }
}

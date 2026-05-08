impl Solution {
    pub fn min_operations(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut ans = 0i32;
        let mut flip = 0i32;
        let mut i = 0usize;
        while i < n {
            if nums[i] == flip {
                ans = ans + 1;
                flip = if flip == 0 { 1 } else { 0 };
            }
            i += 1;
        }
        ans
    }
}

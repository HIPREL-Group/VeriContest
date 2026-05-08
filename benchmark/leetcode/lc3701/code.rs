impl Solution {
    pub fn alternating_sum(nums: Vec<i32>) -> i32 {
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        let n: usize = nums.len();
        while i < n {
            let old_i: usize = i;
            let prev: i32 = ans;
            if old_i % 2 == 0 {
                ans = prev + nums[old_i];
            } else {
                ans = prev - nums[old_i];
            }
            i = i + 1;
        }
        ans
    }
}

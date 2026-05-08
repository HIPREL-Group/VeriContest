impl Solution {
    pub fn alternating_subarray(nums: Vec<i32>) -> i32 {
        let mut dp: i32 = -1;
        let mut res: i32 = -1;
        let mut i: usize = 1;
        while i < nums.len() {
            if dp > 0 && nums[i] == nums[i - 2] {
                dp = dp + 1;
            } else if nums[i] == nums[i - 1] + 1 {
                dp = 2;
            } else {
                dp = -1;
            }
            if dp > res {
                res = dp;
            }
            i = i + 1;
        }
        res
    }
}

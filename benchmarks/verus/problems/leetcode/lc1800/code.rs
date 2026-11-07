impl Solution {
    pub fn max_ascending_sum(nums: Vec<i32>) -> i32 {
        let mut result = nums[0];
        let mut cur = nums[0];
        let mut i = 1usize;
        while i < nums.len() {
            if nums[i] > nums[i - 1] {
                cur += nums[i];
            } else {
                cur = nums[i];
            }
            if cur > result {
                result = cur;
            }
            i += 1;
        }
        result
    }
}

impl Solution {
    pub fn count_subarrays(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i + 2 < n {
            if 2 * (nums[i] + nums[i + 2]) == nums[i + 1] {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

impl Solution {
    pub fn longest_ones(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut left: usize = 0;
        let mut zeros: i32 = 0;
        let mut result: i32 = 0;
        let mut right: usize = 0;

        while right < n {
            if nums[right] == 0 {
                zeros = zeros + 1;
            }
            right = right + 1;

            while zeros > k {
                if nums[left] == 0 {
                    zeros = zeros - 1;
                }
                left = left + 1;
            }

            let window = (right - left) as i32;
            if window > result {
                result = window;
            }
        }

        result
    }
}

impl Solution {
    pub fn longest_subarray(nums: Vec<i32>) -> i32 {
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

            while zeros > 1 {
                if nums[left] == 0 {
                    zeros = zeros - 1;
                }
                left = left + 1;
            }

            let window = if right > left {
                (right - left) as i32 - 1
            } else {
                0
            };
            if window > result {
                result = window;
            }
        }

        result
    }
}

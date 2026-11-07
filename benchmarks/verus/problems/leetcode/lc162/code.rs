impl Solution {
    pub fn find_peak_element(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right {
            let mid = left + (right - left) / 2;
            if nums[mid] < nums[mid + 1] {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        left as i32
    }
}

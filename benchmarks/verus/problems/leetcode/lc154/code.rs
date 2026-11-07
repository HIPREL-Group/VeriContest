impl Solution {
    pub fn find_min(nums: Vec<i32>) -> i32 {
        let mut left: usize = 0;
        let mut right: usize = nums.len() - 1;
        while left < right {
            let mid = left + (right - left) / 2;
            if nums[mid] > nums[right] {
                left = mid + 1;
            } else if nums[mid] < nums[right] {
                right = mid;
            } else {
                right = right - 1;
            }
        }
        nums[left]
    }
}

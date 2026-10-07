impl Solution {
    pub fn sort_the_array(nums: Vec<i64>) -> Option<(usize, usize)> {
        let n = nums.len();
        let mut left = 0usize;
        while left + 1 < n && nums[left] <= nums[left + 1] {
            left += 1;
        }
        if left + 1 == n {
            return Some((1, 1));
        }
        let mut right = n - 1;
        while right > 0 && nums[right - 1] <= nums[right] {
            right -= 1;
        }
        let mut i = 0usize;
        while i + 1 < n {
            let a = if left <= i && i <= right {
                nums[right - (i - left)]
            } else {
                nums[i]
            };
            let j = i + 1;
            let b = if left <= j && j <= right {
                nums[right - (j - left)]
            } else {
                nums[j]
            };
            if a > b {
                return None;
            }
            i += 1;
        }
        Some((left + 1, right + 1))
    }
}

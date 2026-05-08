impl Solution {
    fn max_elem_exec(nums: &Vec<i32>) -> i32 {
        let mut m = nums[0];
        let mut i: usize = 1;
        while i < nums.len() {
            if nums[i] > m {
                m = nums[i];
            }
            i = i + 1;
        }
        m
    }

    fn can_make(nums: &Vec<i32>, x: i32) -> bool {
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            s = s + nums[i] as i64;
            let denom = i as i64 + 1;
            if (s + denom - 1) / denom > x as i64 {
                return false;
            }
            i = i + 1;
        }
        true
    }

    pub fn minimize_array_value(nums: Vec<i32>) -> i32 {
        let mut left: i32 = 0;
        let mut right: i32 = Self::max_elem_exec(&nums);
        while left < right {
            let mid = left + (right - left) / 2;
            if Self::can_make(&nums, mid) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left
    }
}

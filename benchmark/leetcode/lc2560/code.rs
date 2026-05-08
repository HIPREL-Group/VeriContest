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

    fn count_with_cap(nums: &Vec<i32>, cap: i32) -> i32 {
        let mut prev2: i32 = 0;
        let mut prev1: i32 = if nums[0] <= cap { 1 } else { 0 };
        let mut i: usize = 1;
        while i < nums.len() {
            let can_take: i32 = if nums[i] <= cap { 1 } else { 0 };
            let take = prev2 + can_take;
            let curr = if take > prev1 { take } else { prev1 };
            prev2 = prev1;
            prev1 = curr;
            i = i + 1;
        }
        prev1
    }

    fn can_rob(nums: &Vec<i32>, cap: i32, k: i32) -> bool {
        Self::count_with_cap(nums, cap) >= k
    }

    pub fn min_capability(nums: Vec<i32>, k: i32) -> i32 {
        let mut left: i32 = 1;
        let mut right: i32 = Self::max_elem_exec(&nums);
        while left < right {
            let mid = left + (right - left) / 2;
            if Self::can_rob(&nums, mid, k) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left
    }
}

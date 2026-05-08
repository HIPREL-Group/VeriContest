impl Solution {
    pub fn count_elements(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n <= 1 {
            return 0;
        }

        let mut min_v = nums[0];
        let mut max_v = nums[0];
        let mut i: usize = 1;
        while i < n {
            if nums[i] < min_v {
                min_v = nums[i];
            }
            if nums[i] > max_v {
                max_v = nums[i];
            }
            i = i + 1;
        }

        let mut ans: i32 = 0;
        i = 0;
        while i < n {
            if nums[i] > min_v && nums[i] < max_v {
                ans = ans + 1;
            }
            i = i + 1;
        }
        ans
    }
}

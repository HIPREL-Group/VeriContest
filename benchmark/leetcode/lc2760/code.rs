impl Solution {
    pub fn longest_alternating_subarray(nums: Vec<i32>, threshold: i32) -> i32 {
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;

        while i < n {
            let mut len: i32 = 0;
            let mut active: bool = false;
            if nums[i] % 2 == 0 && nums[i] <= threshold {
                len = 1;
                active = true;
            }

            let mut j: usize = i + 1;
            while j < n {
                if active && nums[j] <= threshold && nums[j] % 2 != nums[j - 1] % 2 {
                    len = len + 1;
                } else {
                    active = false;
                }
                j = j + 1;
            }

            if len > ans {
                ans = len;
            }

            i = i + 1;
        }

        ans
    }
}

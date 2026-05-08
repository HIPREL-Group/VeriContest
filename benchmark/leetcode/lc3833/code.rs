impl Solution {
    pub fn dominant_indices(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if i + 1 < n {
                let mut sum: i32 = 0;
                let mut j: usize = i + 1;
                while j < n {
                    sum = sum + nums[j];
                    j = j + 1;
                }
                let right_len: i32 = (n - i - 1) as i32;
                let avg: i32 = sum / right_len;
                if nums[i] > avg {
                    ans = ans + 1;
                }
            }
            i = i + 1;
        }
        ans
    }
}

impl Solution {
    pub fn find_length(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let m = nums1.len();
        let n = nums2.len();
        let total = (m + 1) * (n + 1);
        let mut dp: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        while idx < total {
            dp.push(0);
            idx += 1;
        }
        let mut max_len = 0i32;
        let mut i = 1usize;
        while i <= m {
            let mut j = 1usize;
            while j <= n {
                let cur_idx = i * (n + 1) + j;
                let prev_idx = (i - 1) * (n + 1) + (j - 1);
                if nums1[i - 1] == nums2[j - 1] {
                    let val = dp[prev_idx] + 1;
                    dp[cur_idx] = val;
                    if val > max_len {
                        max_len = val;
                    }
                } else {
                    dp[cur_idx] = 0;
                }
                j += 1;
            }
            i += 1;
        }
        max_len
    }
}

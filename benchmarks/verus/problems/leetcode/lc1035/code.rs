impl Solution {
    pub fn max_uncrossed_lines(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let m = nums1.len();
        let n = nums2.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            dp.push(0);
            k = k + 1;
        }
        let mut i: usize = 1;
        while i <= m {
            let mut prev: i32 = 0;
            let mut j: usize = 1;
            while j <= n {
                let curr = dp[j];
                if nums1[i - 1] == nums2[j - 1] {
                    dp[j] = prev + 1;
                } else {
                    let a = curr;
                    let b = dp[j - 1];
                    if a >= b {
                        dp[j] = a;
                    } else {
                        dp[j] = b;
                    }
                }
                prev = curr;
                j = j + 1;
            }
            i = i + 1;
        }
        dp[n]
    }
}

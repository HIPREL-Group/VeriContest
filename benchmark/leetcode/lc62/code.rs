impl Solution {
    pub fn unique_paths(m: i32, n: i32) -> i32 {
        let m = m as usize;
        let n = n as usize;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            dp.push(1i32);
            k += 1;
        }
        let mut i: usize = 1;
        while i < m {
            let mut j: usize = 1;
            while j < n {
                let dpj: i32 = dp[j];
                let dpjm1: i32 = dp[j - 1];
                dp[j] = dpj + dpjm1;
                j += 1;
            }
            i += 1;
        }
        dp[n - 1]
    }
}

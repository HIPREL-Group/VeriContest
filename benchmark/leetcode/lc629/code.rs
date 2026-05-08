impl Solution {
    pub fn k_inverse_pairs(n: i32, k: i32) -> i32 {
        let m: i64 = 1000000007;
        let mut dp: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t <= 1000 {
            dp.push(0);
            t += 1;
        }
        dp[0] = 1;

        let mut i: i32 = 1;
        while i <= n {
            let mut next: Vec<i32> = Vec::new();
            let mut t2: usize = 0;
            while t2 <= 1000 {
                next.push(0);
                t2 += 1;
            }
            let mut j: i32 = 0;
            let mut window: i64 = 0;
            while j <= k {
                window += dp[j as usize] as i64;
                if j - i >= 0 {
                    window -= dp[(j - i) as usize] as i64;
                }
                window = window % m;
                if window < 0 {
                    window += m;
                }
                next[j as usize] = window as i32;
                j += 1;
            }
            dp = next;
            i += 1;
        }

        dp[k as usize]
    }
}

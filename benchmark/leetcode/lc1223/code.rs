impl Solution {
    pub fn die_simulator(n: i32, roll_max: Vec<i32>) -> i32 {
        let modp: i64 = 1_000_000_007;
        let n_us = n as usize;
        let dp_size = (n_us + 1) * 6;
        let mut dp: Vec<i64> = Vec::new();
        let mut idx = 0usize;
        while idx < dp_size {
            dp.push(0i64);
            idx = idx + 1;
        }
        let mut total: Vec<i64> = Vec::new();
        idx = 0;
        while idx <= n_us {
            total.push(0i64);
            idx = idx + 1;
        }
        total[0] = 1;
        let mut j = 0usize;
        while j < 6 {
            dp[6 + j] = 1;
            j = j + 1;
        }
        total[1] = 6;
        let mut i = 2usize;
        while i <= n_us {
            let mut j = 0usize;
            while j < 6 {
                let rm_j = roll_max[j] as usize;
                let bound = if rm_j < i { rm_j } else { i };
                let mut val: i64 = 0;
                let mut k = 1usize;
                while k <= bound {
                    let prev = i - k;
                    let diff = (total[prev] - dp[prev * 6 + j] + modp) % modp;
                    val = (val + diff) % modp;
                    k = k + 1;
                }
                dp[i * 6 + j] = val;
                j = j + 1;
            }
            let mut t: i64 = 0;
            let mut j2 = 0usize;
            while j2 < 6 {
                t = (t + dp[i * 6 + j2]) % modp;
                j2 = j2 + 1;
            }
            total[i] = t;
            i = i + 1;
        }
        (total[n_us] % modp) as i32
    }
}

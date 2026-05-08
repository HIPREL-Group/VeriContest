impl Solution {
    pub fn min_difficulty(job_difficulty: Vec<i32>, d: i32) -> i32 {
        let n = job_difficulty.len() as i32;
        if d > n {
            return -1i32;
        }
        let mut prev_dp: Vec<i32> = Vec::new();
        prev_dp.push(job_difficulty[0]);
        let mut j: i32 = 1;
        while j < n {
            let prev = prev_dp[(j - 1) as usize];
            let curr = job_difficulty[j as usize];
            if prev >= curr {
                prev_dp.push(prev);
            } else {
                prev_dp.push(curr);
            }
            j = j + 1;
        }
        let mut day: i32 = 1;
        while day < d {
            let mut curr_dp: Vec<i32> = Vec::new();
            let mut fill: i32 = 0;
            while fill < day {
                curr_dp.push(1_000_001i32);
                fill = fill + 1;
            }
            let mut j: i32 = day;
            while j < n {
                let mut best: i32 = 1_000_001;
                let mut max_right: i32 = job_difficulty[j as usize];
                let mut k: i32 = j - 1;
                while k >= day - 1 {
                    let prev_val = prev_dp[k as usize];
                    let candidate = prev_val + max_right;
                    if candidate < best {
                        best = candidate;
                    }
                    let jk = job_difficulty[k as usize];
                    if jk > max_right {
                        max_right = jk;
                    }
                    k = k - 1;
                }
                curr_dp.push(best);
                j = j + 1;
            }
            prev_dp = curr_dp;
            day = day + 1;
        }
        prev_dp[(n - 1) as usize]
    }
}

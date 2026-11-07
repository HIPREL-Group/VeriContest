impl Solution {
    pub fn max_points(points: Vec<Vec<i32>>) -> i64 {
        let m = points.len();
        let n = points[0].len();

        let mut dp: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            dp.push(points[0][j] as i64);
            j += 1;
        }

        let mut i: usize = 1;
        while i < m {
            let mut left: Vec<i64> = Vec::new();
            left.push(dp[0]);
            let mut j: usize = 1;
            while j < n {
                let prev = left[j - 1] - 1;
                let cur = dp[j];
                let val = if prev > cur { prev } else { cur };
                left.push(val);
                j += 1;
            }

            let mut right: Vec<i64> = Vec::new();
            let mut k: usize = 0;
            while k < n {
                right.push(0i64);
                k += 1;
            }
            right[n - 1] = dp[n - 1];
            let mut k: usize = 0;
            while k + 1 < n {
                let j = n - 2 - k;
                let nxt = right[j + 1] - 1;
                let cur = dp[j];
                right[j] = if nxt > cur { nxt } else { cur };
                k += 1;
            }

            let mut new_dp: Vec<i64> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let best = if left[j] > right[j] { left[j] } else { right[j] };
                new_dp.push(points[i][j] as i64 + best);
                j += 1;
            }

            dp = new_dp;
            i += 1;
        }

        let mut result: i64 = dp[0];
        let mut j: usize = 1;
        while j < n {
            if dp[j] > result {
                result = dp[j];
            }
            j += 1;
        }

        result
    }
}

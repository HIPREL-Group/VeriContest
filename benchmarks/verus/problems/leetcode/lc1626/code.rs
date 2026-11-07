impl Solution {
    pub fn best_team_score(scores: Vec<i32>, ages: Vec<i32>) -> i32 {
        let n = scores.len();
        let mut scores = scores;
        let mut ages = ages;
        let mut i: usize = 0;
        while i < n {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n {
                if ages[j] < ages[min_idx]
                    || (ages[j] == ages[min_idx] && scores[j] < scores[min_idx])
                {
                    min_idx = j;
                }
                j += 1;
            }
            let tmp_a = ages[i];
            let tmp_s = scores[i];
            ages[i] = ages[min_idx];
            scores[i] = scores[min_idx];
            ages[min_idx] = tmp_a;
            scores[min_idx] = tmp_s;
            i += 1;
        }
        let mut dp: Vec<i64> = Vec::new();
        i = 0;
        while i < n {
            dp.push(scores[i] as i64);
            i += 1;
        }
        i = 1;
        while i < n {
            let mut j: usize = 0;
            while j < i {
                if scores[j] <= scores[i] {
                    if dp[j] + scores[i] as i64 > dp[i] {
                        dp[i] = dp[j] + scores[i] as i64;
                    }
                }
                j += 1;
            }
            i += 1;
        }
        let mut best: i64 = dp[0];
        let mut k: usize = 1;
        while k < n {
            if dp[k] > best {
                best = dp[k];
            }
            k += 1;
        }
        best as i32
    }
}

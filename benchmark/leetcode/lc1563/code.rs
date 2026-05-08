impl Solution {
    pub fn stone_game_v(stone_value: Vec<i32>) -> i32 {
        let n = stone_value.len();
        if n <= 1 {
            return 0;
        }
        let mut pre: Vec<i64> = Vec::new();
        pre.push(0i64);
        let mut idx: usize = 0;
        while idx < n {
            pre.push(pre[idx] + stone_value[idx] as i64);
            idx = idx + 1;
        }
        let mut dp: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n * n {
            dp.push(0i32);
            idx = idx + 1;
        }
        let mut gap: usize = 1;
        while gap < n {
            let mut i: usize = 0;
            while i + gap < n {
                let j: usize = i + gap;
                let mut best: i32 = 0;
                let mut k: usize = i;
                while k < j {
                    let left_sum: i64 = pre[k + 1] - pre[i];
                    let right_sum: i64 = pre[j + 1] - pre[k + 1];
                    let score: i32;
                    if left_sum < right_sum {
                        score = left_sum as i32 + dp[i * n + k];
                    } else if left_sum > right_sum {
                        score = right_sum as i32 + dp[(k + 1) * n + j];
                    } else {
                        let a: i32 = left_sum as i32 + dp[i * n + k];
                        let b: i32 = right_sum as i32 + dp[(k + 1) * n + j];
                        if a >= b {
                            score = a;
                        } else {
                            score = b;
                        }
                    }
                    if score > best {
                        best = score;
                    }
                    k = k + 1;
                }
                dp[i * n + j] = best;
                i = i + 1;
            }
            gap = gap + 1;
        }
        dp[n - 1]
    }
}

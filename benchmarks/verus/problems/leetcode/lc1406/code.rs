impl Solution {
    pub fn stone_game_iii(stone_value: Vec<i32>) -> String {
        let n = stone_value.len();
        let mut dp: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            dp.push(0i64);
            k = k + 1;
        }
        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let mut best: i64 = stone_value[i] as i64 - dp[i + 1];
            if i + 1 < n {
                let t2: i64 = stone_value[i] as i64 + stone_value[i + 1] as i64 - dp[i + 2];
                if t2 > best {
                    best = t2;
                }
            }
            if i + 2 < n {
                let t3: i64 = stone_value[i] as i64 + stone_value[i + 1] as i64 + stone_value[i + 2] as i64 - dp[i + 3];
                if t3 > best {
                    best = t3;
                }
            }
            dp[i] = best;
        }
        if dp[0] > 0 {
            "Alice".to_string()
        } else if dp[0] < 0 {
            "Bob".to_string()
        } else {
            "Tie".to_string()
        }
    }
}

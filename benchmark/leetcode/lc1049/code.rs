impl Solution {
    pub fn last_stone_weight_ii(stones: Vec<i32>) -> i32 {
        let n = stones.len();
        let mut total = 0i32;
        let mut i = 0usize;
        while i < n {
            total = total + stones[i];
            i = i + 1;
        }
        let half = (total / 2) as usize;
        let dp_len = half + 1;
        let mut dp: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < dp_len {
            dp.push(false);
            k = k + 1;
        }
        dp[0] = true;
        let mut idx: usize = 0;
        while idx < n {
            let num = stones[idx] as usize;
            let mut s = dp_len;
            while s > 0 {
                let cur = s - 1;
                if num <= cur {
                    let old_val = dp[cur];
                    let add_val = dp[cur - num];
                    let new_val = old_val || add_val;
                    dp[cur] = new_val;
                }
                s = cur;
            }
            idx = idx + 1;
        }
        let mut j = half;
        while j > 0 {
            if dp[j] {
                return total - 2 * (j as i32);
            }
            j = j - 1;
        }
        total
    }
}

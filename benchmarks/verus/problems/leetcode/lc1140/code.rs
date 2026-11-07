impl Solution {
    pub fn stone_game_ii(piles: Vec<i32>) -> i32 {
        let n = piles.len();
        let stride = n + 1;
        let mut suffix_sums: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < stride {
            suffix_sums.push(0i32);
            k += 1;
        }
        let mut si = n;
        while si > 0 {
            si -= 1;
            suffix_sums[si] = suffix_sums[si + 1] + piles[si];
        }
        let total = stride * stride;
        let mut dp: Vec<i32> = Vec::new();
        let mut k2: usize = 0;
        while k2 < total {
            dp.push(0i32);
            k2 += 1;
        }
        let mut i: usize = n;
        while i > 0 {
            i -= 1;
            let mut m: usize = 1;
            while m <= n {
                if i + 2 * m >= n {
                    dp[i * stride + m] = suffix_sums[i];
                } else {
                    let mut best: i32 = suffix_sums[i] - dp[(i + 1) * stride + m];
                    let mut x: usize = 2;
                    while x <= 2 * m {
                        let new_m: usize = if x > m { x } else { m };
                        let score: i32 = suffix_sums[i] - dp[(i + x) * stride + new_m];
                        if score > best {
                            best = score;
                        }
                        x += 1;
                    }
                    dp[i * stride + m] = best;
                }
                m += 1;
            }
        }
        dp[1]
    }
}

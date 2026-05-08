impl Solution {
    fn triple_product(a: i32, b: i32, c: i32) -> i32 {
        let ab = a * b;
        ab * c
    }

    pub fn min_score_triangulation(values: Vec<i32>) -> i32 {
        let n = values.len();
        let nn = n * n;
        let mut dp: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        while idx < nn {
            dp.push(0i32);
            idx = idx + 1;
        }
        let mut gap = 2usize;
        while gap < n {
            let mut i = 0usize;
            while i + gap < n {
                let j = i + gap;
                let k_first: usize = i + 1;
                let dl = dp[i * n + k_first];
                let dr = dp[k_first * n + j];
                let prod = Self::triple_product(values[i], values[k_first], values[j]);
                let score_first = dl + dr + prod;
                let mut best: i32 = score_first;
                let mut k: usize = i + 2;
                while k < j {
                    let dl2 = dp[i * n + k];
                    let dr2 = dp[k * n + j];
                    let prod2 = Self::triple_product(values[i], values[k], values[j]);
                    let score = dl2 + dr2 + prod2;
                    if score < best {
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

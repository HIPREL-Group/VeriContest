impl Solution {
    fn create_zero_vec(sz: usize) -> Vec<i64> {
        let mut v: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < sz {
            v.push(0i64);
            j = j + 1;
        }
        v
    }

    pub fn num_of_arrays(n: i32, m: i32, k: i32) -> i32 {
        let modv: i64 = 1_000_000_007;
        let ni = n as usize;
        let mi = m as usize;
        let ki = k as usize;
        let stride: usize = ki + 1;
        let sz: usize = (mi + 1) * stride;
        if ki == 0 {
            return 0i32;
        }
        let mut prev_dp = Self::create_zero_vec(sz);
        let mut prev_prefix = Self::create_zero_vec(sz);
        let mut j: usize = 1;
        while j <= mi {
            prev_dp[j * stride + 1] = 1i64;
            prev_prefix[j * stride + 1] = j as i64;
            j = j + 1;
        }
        let mut len: usize = 2;
        while len <= ni {
            let mut dp = Self::create_zero_vec(sz);
            let mut prefix = Self::create_zero_vec(sz);
            let mut max_num: usize = 1;
            while max_num <= mi {
                let mut cost: usize = 1;
                while cost <= ki {
                    let cur = max_num * stride + cost;
                    let dp_term = (max_num as i64 * prev_dp[cur]) % modv;
                    let prefix_term: i64 = if max_num > 1 && cost > 1 {
                        prev_prefix[(max_num - 1) * stride + (cost - 1)]
                    } else {
                        0i64
                    };
                    let new_dp_val = (dp_term + prefix_term) % modv;
                    dp[cur] = new_dp_val;
                    let new_prefix_val = (prefix[(max_num - 1) * stride + cost] + new_dp_val) % modv;
                    prefix[max_num * stride + cost] = new_prefix_val;
                    cost = cost + 1;
                }
                max_num = max_num + 1;
            }
            prev_dp = dp;
            prev_prefix = prefix;
            len = len + 1;
        }
        prev_prefix[mi * stride + ki] as i32
    }
}
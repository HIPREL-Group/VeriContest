impl Solution {
    pub fn min_cost(
        houses: Vec<i32>,
        cost: Vec<Vec<i32>>,
        m: i32,
        n: i32,
        target: i32,
    ) -> i32 {
        let m_us = m as usize;
        let n_us = n as usize;
        let target_us = target as usize;
        let stride: usize = target_us + 1;
        let dp_size: usize = (n_us + 1) * stride;

        let mut prev_dp: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < dp_size {
            prev_dp.push(1_000_001i32);
            idx += 1;
        }

        let mut j: usize = 1;
        while j <= n_us {
            if houses[0] != 0 {
                if houses[0] as usize == j {
                    prev_dp[j * stride + 1] = 0i32;
                }
            } else {
                prev_dp[j * stride + 1] = cost[0][j - 1];
            }
            j += 1;
        }

        let mut i: usize = 1;
        while i < m_us {
            let mut curr_dp: Vec<i32> = Vec::new();
            let mut idx: usize = 0;
            while idx < dp_size {
                curr_dp.push(1_000_001i32);
                idx += 1;
            }

            let mut j: usize = 1;
            while j <= n_us {
                if houses[i] == 0 || houses[i] as usize == j {
                    let paint_cost: i32 =
                        if houses[i] != 0 { 0i32 } else { cost[i][j - 1] };

                    let mut k: usize = 1;
                    while k <= target_us {
                        let same: i32 = prev_dp[j * stride + k];

                        let mut diff: i32 = 1_000_001i32;
                        let mut c: usize = 1;
                        while c <= n_us {
                            if c != j {
                                let val: i32 = prev_dp[c * stride + (k - 1)];
                                if val < diff {
                                    diff = val;
                                }
                            }
                            c += 1;
                        }

                        let best: i32 = if same <= diff { same } else { diff };
                        if best < 1_000_001i32 {
                            let total: i32 = paint_cost + best;
                            if total < 1_000_001i32 {
                                curr_dp[j * stride + k] = total;
                            }
                        }

                        k += 1;
                    }
                }
                j += 1;
            }

            prev_dp = curr_dp;
            i += 1;
        }

        let mut ans: i32 = 1_000_001i32;
        let mut j: usize = 1;
        while j <= n_us {
            let val: i32 = prev_dp[j * stride + target_us];
            if val < ans {
                ans = val;
            }
            j += 1;
        }

        if ans >= 1_000_001i32 { -1i32 } else { ans }
    }
}

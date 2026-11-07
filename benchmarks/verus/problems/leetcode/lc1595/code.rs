impl Solution {
    pub fn connect_two_groups(cost: Vec<Vec<i32>>) -> i32 {
        let m = cost.len();
        let n = cost[0].len();
        let total_masks: usize = 1usize << n;

        let mut min_cost: Vec<i32> = Vec::new();
        let mut jj: usize = 0;
        while jj < n {
            let mut mc: i32 = cost[0][jj];
            let mut ii: usize = 1;
            while ii < m {
                if cost[ii][jj] < mc {
                    mc = cost[ii][jj];
                }
                ii = ii + 1;
            }
            min_cost.push(mc);
            jj = jj + 1;
        }

        let mut dp: Vec<i32> = Vec::new();
        let mut mask: usize = 0;
        while mask < total_masks {
            let mut uc: i32 = 0;
            let mut j: usize = 0;
            while j < n {
                if ((mask as u32) & (1u32 << (j as u32))) == 0u32 {
                    uc = uc + min_cost[j];
                }
                j = j + 1;
            }
            dp.push(uc);
            mask = mask + 1;
        }

        let mut row: usize = m;
        while row > 0 {
            row = row - 1;
            let mut new_dp: Vec<i32> = Vec::new();
            let mut mask: usize = 0;
            while mask < total_masks {
                let mut best: i32 = 100_000;
                let mut j: usize = 0;
                while j < n {
                    let new_mask: usize = mask | (1usize << j);
                    let val: i32 = cost[row][j] + dp[new_mask];
                    if val < best {
                        best = val;
                    }
                    j = j + 1;
                }
                new_dp.push(best);
                mask = mask + 1;
            }
            dp = new_dp;
        }

        dp[0]
    }
}

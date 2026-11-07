impl Solution {
    fn max2_i64(a: i64, b: i64) -> i64 {
        if a >= b { a } else { b }
    }

    fn min2_i64(a: i64, b: i64) -> i64 {
        if a <= b { a } else { b }
    }

    fn max4_i64(a: i64, b: i64, c: i64, d: i64) -> i64 {
        Self::max2_i64(Self::max2_i64(a, b), Self::max2_i64(c, d))
    }

    fn min4_i64(a: i64, b: i64, c: i64, d: i64) -> i64 {
        Self::min2_i64(Self::min2_i64(a, b), Self::min2_i64(c, d))
    }

    pub fn max_product_path(grid: Vec<Vec<i32>>) -> i32 {
        let m = grid.len();
        let n = grid[0].len();

        let mut dp_max: Vec<i64> = Vec::new();
        let mut dp_min: Vec<i64> = Vec::new();

        dp_max.push(grid[0][0] as i64);
        dp_min.push(grid[0][0] as i64);

        let mut j = 1usize;
        while j < n {
            let val = grid[0][j] as i64;
            dp_max.push(dp_max[j - 1] * val);
            dp_min.push(dp_min[j - 1] * val);
            j += 1;
        }

        let mut i = 1usize;
        while i < m {
            let v0 = grid[i][0] as i64;
            let old_mx = dp_max[0];
            let old_mn = dp_min[0];
            dp_max[0] = old_mx * v0;
            dp_min[0] = old_mn * v0;

            let mut j = 1usize;
            while j < n {
                let above_mx = dp_max[j];
                let above_mn = dp_min[j];
                let left_mx = dp_max[j - 1];
                let left_mn = dp_min[j - 1];
                let v = grid[i][j] as i64;
                let a = above_mx * v;
                let b = above_mn * v;
                let c = left_mx * v;
                let d = left_mn * v;
                let new_mx = Self::max4_i64(a, b, c, d);
                let new_mn = Self::min4_i64(a, b, c, d);
                dp_max[j] = new_mx;
                dp_min[j] = new_mn;
                j += 1;
            }

            i += 1;
        }

        if dp_max[n - 1] < 0 {
            -1i32
        } else {
            (dp_max[n - 1] % 1_000_000_007i64) as i32
        }
    }
}

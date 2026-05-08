const INF64: i64 = 4_000_000_000_000_000_000i64;

impl Solution {
    pub fn gas_pipeline(n: usize, a: i64, b: i64, s: Vec<i32>) -> i64 {
        let mut dp1 = b;
        let mut dp2 = INF64;
        let mut i: usize = 0;
        while i < n {
            let si = s[i];
            let (n1, n2) = if si == 1 {
                if dp2 < INF64 {
                    (INF64, dp2 + a + 2 * b)
                } else {
                    (INF64, INF64)
                }
            } else {
                let mut n1 = INF64;
                let mut n2 = INF64;
                if dp1 < INF64 {
                    let v11 = dp1 + a + b;
                    if v11 < n1 {
                        n1 = v11;
                    }
                    let v12 = dp1 + 2 * a + 2 * b;
                    if v12 < n2 {
                        n2 = v12;
                    }
                }
                if dp2 < INF64 {
                    let v22 = dp2 + a + 2 * b;
                    if v22 < n2 {
                        n2 = v22;
                    }
                    let v21 = dp2 + 2 * a + b;
                    if v21 < n1 {
                        n1 = v21;
                    }
                }
                (n1, n2)
            };
            dp1 = n1;
            dp2 = n2;
            i = i + 1;
        }
        dp1
    }
}

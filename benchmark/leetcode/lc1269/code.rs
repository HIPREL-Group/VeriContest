impl Solution {
    pub fn num_ways(steps: i32, arr_len: i32) -> i32 {
        let modulo: i64 = 1_000_000_007;
        let max_p: i32 = if steps / 2 < arr_len - 1 {
            steps / 2
        } else {
            arr_len - 1
        };
        let size: usize = (max_p + 1) as usize;

        let mut cur: Vec<i64> = Vec::new();
        let mut init_i: usize = 0;
        while init_i < size {
            cur.push(0i64);
            init_i += 1;
        }
        cur[0] = 1i64;

        let mut s: i32 = 0;
        while s < steps {
            let mut nxt: Vec<i64> = Vec::new();
            let mut init_j: usize = 0;
            while init_j < size {
                nxt.push(0i64);
                init_j += 1;
            }
            let mut j: i32 = 0;
            while j <= max_p {
                let left: i64 = if j > 0 {
                    cur[(j - 1) as usize]
                } else {
                    0i64
                };
                let right: i64 = if j < max_p {
                    cur[(j + 1) as usize]
                } else {
                    0i64
                };
                let stay: i64 = cur[j as usize];
                nxt[j as usize] = (left + right + stay) % modulo;
                j += 1;
            }
            cur = nxt;
            s += 1;
        }
        cur[0] as i32
    }
}

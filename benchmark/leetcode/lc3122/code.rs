impl Solution {
    pub fn minimum_operations(grid: Vec<Vec<i32>>) -> i32 {
        let m = grid.len();
        let n = grid[0].len();
        let m_i64 = m as i64;

        let mut dp_prev: Vec<i64> = Vec::new();
        let mut v: usize = 0;
        while v < 10 {
            let mut matches: i64 = 0;
            let mut i: usize = 0;
            while i < m {
                if grid[i][0] == v as i32 {
                    matches = matches + 1;
                }
                i = i + 1;
            }
            let cost = m_i64 - matches;
            dp_prev.push(cost);
            v = v + 1;
        }

        let mut col: usize = 1;
        while col < n {
            let mut dp_cur: Vec<i64> = Vec::new();
            v = 0;
            while v < 10 {
                let mut matches: i64 = 0;
                let mut i: usize = 0;
                while i < m {
                    if grid[i][col] == v as i32 {
                        matches = matches + 1;
                    }
                    i = i + 1;
                }
                let cost = m_i64 - matches;

                let mut best: i64 = 1_000_000_000;
                let mut u: usize = 0;
                while u < 10 {
                    if u != v && dp_prev[u] < best {
                        best = dp_prev[u];
                    }
                    u = u + 1;
                }

                let value = cost + best;
                dp_cur.push(value);
                v = v + 1;
            }
            dp_prev = dp_cur;
            col = col + 1;
        }

        let mut answer: i64 = 1_000_000_000;
        v = 0;
        while v < 10 {
            if dp_prev[v] < answer {
                answer = dp_prev[v];
            }
            v = v + 1;
        }

        answer as i32
    }
}

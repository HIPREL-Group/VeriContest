impl Solution {
    pub fn min_ops(a: Vec<i64>) -> u64 {
        let n = a.len();
        let mut segments: Vec<u64> = Vec::new();
        let mut init: usize = 0;
        while init <= n {
            segments.push(0);
            init = init + 1;
        }
        let mut i: usize = 0;
        while i < n {
            if i == 0 || a[i] != a[i - 1] {
                let idx = a[i] as usize;
                segments[idx] = segments[idx] + 1;
            }
            i = i + 1;
        }

        let mut best: u64 = (n + 1) as u64;
        let mut x: usize = 1;
        while x <= n {
            if segments[x] > 0 {
                let mut ops = segments[x] + 1;
                if a[0] == x as i64 {
                    ops = ops - 1;
                }
                if a[n - 1] == x as i64 {
                    ops = ops - 1;
                }
                if ops < best {
                    best = ops;
                }
            }
            x = x + 1;
        }
        best
    }
}

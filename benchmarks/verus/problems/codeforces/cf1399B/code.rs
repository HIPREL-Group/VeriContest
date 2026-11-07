impl Solution {
    pub fn min_moves_to_equalize(n: usize, a: Vec<u64>, b: Vec<u64>) -> u64 {
        let mut ma: u64 = a[0];
        let mut mb: u64 = b[0];
        let mut i: usize = 1;
        while i < n {
            if a[i] < ma { ma = a[i]; }
            if b[i] < mb { mb = b[i]; }
            i += 1;
        }
        let mut total: u64 = 0;
        let mut j: usize = 0;
        while j < n {
            let da = a[j] - ma;
            let db = b[j] - mb;
            let m = if da >= db { da } else { db };
            total = total + m;
            j += 1;
        }
        total
    }
}

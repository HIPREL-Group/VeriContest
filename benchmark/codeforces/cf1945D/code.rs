impl Solution {
    pub fn min_coins(a: Vec<i64>, b: Vec<i64>, m: usize) -> i64 {
        let n = a.len();
        
        
        let mut suffix: Vec<i64> = Vec::with_capacity(n + 1);
        let mut k: usize = 0;
        while k <= n {
            suffix.push(0);
            k = k + 1;
        }
        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let m_val: i64 = if a[i] < b[i] { a[i] } else { b[i] };
            suffix[i] = suffix[i + 1] + m_val;
        }
        
        let mut best: i64 = a[0] + suffix[1];
        let mut j: usize = 1;
        while j < m {
            let cost: i64 = a[j] + suffix[j + 1];
            if cost < best {
                best = cost;
            }
            j = j + 1;
        }
        best
    }
}

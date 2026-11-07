impl Solution {
    pub fn min_operations(k: i32) -> i32 {
        let mut best: i32 = k - 1;
        let mut m: i32 = 2;
        while m <= k {
            let ops: i32 = (m - 1) + (k - 1) / m;
            if ops < best {
                best = ops;
            }
            m = m + 1;
        }
        best
    }
}

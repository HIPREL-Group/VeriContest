impl Solution {
    pub fn max_count(m: i32, n: i32, ops: Vec<Vec<i32>>) -> i32 {
        if ops.len() == 0 {
            return m * n;
        }
        let mut min_a = m;
        let mut min_b = n;
        let mut i = 0usize;
        while i < ops.len() {
            let a = ops[i][0];
            let b = ops[i][1];
            if a < min_a {
                min_a = a;
            }
            if b < min_b {
                min_b = b;
            }
            i += 1;
        }
        min_a * min_b
    }
}

impl Solution {
    pub fn complementary_xor_ops(a: Vec<i64>, b: Vec<i64>) -> (bool, Vec<(usize, usize)>) {
        let n = a.len();
        let first_xor = if a[0] == b[0] { 0i64 } else { 1i64 };
        let mut i: usize = 1;
        while i < n {
            let cur_xor = if a[i] == b[i] { 0i64 } else { 1i64 };
            if cur_xor != first_xor {
                return (false, Vec::new());
            }
            i = i + 1;
        }
        let mut ops: Vec<(usize, usize)> = Vec::with_capacity(n + 3);
        let mut ones: usize = 0;
        let mut j: usize = 0;
        while j < n {
            if a[j] == 1 {
                ones = ones + 1;
                ops.push((j + 1, j + 1));
            }
            j = j + 1;
        }
        let parity = (ones % 2) as i64;
        if parity != first_xor {
            ops.push((1, 1));
            ops.push((2, n));
            ops.push((1, n));
        }
        (true, ops)
    }
}

impl Solution {
    pub fn min_moves_balance_remainders(a: Vec<i32>) -> i32 {
        let n = a.len();
        let tgt = n / 3;
        let mut c0: usize = 0;
        let mut c1: usize = 0;
        let mut c2: usize = 0;
        let mut i: usize = 0;
        while i < n {
            let r = a[i] % 3;
            if r == 0 {
                c0 = c0 + 1;
            } else if r == 1 {
                c1 = c1 + 1;
            } else {
                c2 = c2 + 1;
            }
            i = i + 1;
        }
        let mut ops: usize = 0;
        let total3: usize = n * 3;
        while (c0 != tgt || c1 != tgt || c2 != tgt) && ops < total3 {
            if c0 > tgt {
                c0 = c0 - 1;
                c1 = c1 + 1;
                ops = ops + 1;
            } else if c1 > tgt {
                c1 = c1 - 1;
                c2 = c2 + 1;
                ops = ops + 1;
            } else {
                c2 = c2 - 1;
                c0 = c0 + 1;
                ops = ops + 1;
            }
        }
        ops as i32
    }
}

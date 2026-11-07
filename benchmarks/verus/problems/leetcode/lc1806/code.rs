impl Solution {
    pub fn reinitialize_permutation(n: i32) -> i32 {
        if n == 2 {
            return 1;
        }
        let mut val: i32 = n / 2;
        let mut ops: i32 = 1;
        while val != 1 {
            if val % 2 == 0 {
                val = val / 2;
            } else {
                val = n / 2 + (val - 1) / 2;
            }
            ops = ops + 1;
        }
        ops
    }
}

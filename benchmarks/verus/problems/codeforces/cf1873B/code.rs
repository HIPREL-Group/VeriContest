impl Solution {
    pub fn max_product_one_increment(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut best: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut p: i64 = 1;
            let mut j: usize = 0;
            while j < n {
                if j == i {
                    p = p * (a[j] + 1);
                } else {
                    p = p * a[j];
                }
                j = j + 1;
            }
            if p > best {
                best = p;
            }
            i = i + 1;
        }
        best
    }
}

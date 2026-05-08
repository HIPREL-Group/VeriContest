impl Solution {
    pub fn almost_equal(n: usize) -> Vec<i64> {
        if n % 2 == 0 {
            return Vec::new();
        }
        let mut res: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if i % 2 == 0 {
                res.push((2 * i + 1) as i64);
            } else {
                res.push((2 * i + 2) as i64);
            }
            i = i + 1;
        }
        i = 0;
        while i < n {
            if i % 2 == 0 {
                res.push((2 * i + 2) as i64);
            } else {
                res.push((2 * i + 1) as i64);
            }
            i = i + 1;
        }
        res
    }
}

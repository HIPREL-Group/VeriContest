impl Solution {
    pub fn min_pile_shuffle_operations(a: &Vec<i64>, b: &Vec<i64>, c: &Vec<i64>, d: &Vec<i64>) -> i64 {
        let n = a.len();
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut av: i64 = a[i];
            let bv: i64 = b[i];
            let cv: i64 = c[i];
            let dv: i64 = d[i];
            if av > cv {
                ans = ans + (av - cv);
                av = cv;
            }
            if bv > dv {
                ans = ans + (bv - dv + av);
            }
            i = i + 1;
        }
        ans
    }
}

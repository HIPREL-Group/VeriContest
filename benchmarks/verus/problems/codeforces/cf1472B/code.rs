impl Solution {
    pub fn fair_division(n: usize, a: Vec<i32>) -> bool {
        let mut c1: i32 = 0;
        let mut c2: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1 {
                c1 = c1 + 1;
            } else {
                c2 = c2 + 1;
            }
            i = i + 1;
        }
        let total = c1 + 2 * c2;
        if total % 2 != 0 {
            return false;
        }
        let half = total / 2;
        let mut m: i32 = 0;
        while m <= c2 {
            let n1 = half - 2 * m;
            if n1 >= 0 && n1 <= c1 {
                return true;
            }
            m = m + 1;
        }
        false
    }
}

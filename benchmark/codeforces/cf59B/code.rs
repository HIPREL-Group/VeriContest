impl Solution {
    pub fn max_loving_petals(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut total = 0i32;
        let mut min_odd = 101i32;
        let mut i = 0usize;
        while i < n {
            total = total + a[i];
            if a[i] % 2 == 1 {
                if a[i] < min_odd {
                    min_odd = a[i];
                }
            }
            i = i + 1;
        }
        let r = if total % 2 == 1 {
            total
        } else {
            if min_odd == 101 {
                0
            } else {
                total - min_odd
            }
        };
        r
    }
}

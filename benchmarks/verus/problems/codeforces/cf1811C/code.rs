impl Solution {
    pub fn restore_array(n: usize, b: Vec<i64>) -> Vec<i64> {
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if i == 0 {
                a.push(b[0]);
            } else if i < n - 1 {
                if b[i - 1] <= b[i] {
                    a.push(b[i - 1]);
                } else {
                    a.push(b[i]);
                }
            } else {
                a.push(b[n - 2]);
            }
            i = i + 1;
        }
        a
    }
}

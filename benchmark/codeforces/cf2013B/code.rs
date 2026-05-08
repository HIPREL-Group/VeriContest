impl Solution {
    pub fn battle_for_survive(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut s = 0i64;
        let mut i = 0usize;
        while i < n {
            s = s + a[i];
            i = i + 1;
        }
        s - 2 * a[n - 2]
    }
}

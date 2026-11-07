impl Solution {
    pub fn spy_index(a: Vec<i64>) -> usize {
        let n = a.len();
        if a[0] != a[1] {
            if a[0] == a[2] {
                return 2;
            } else {
                return 1;
            }
        }

        let mut i: usize = 2;
        while i < n {
            if a[i] != a[0] {
                return i + 1;
            }
            i += 1;
        }

        1
    }
}

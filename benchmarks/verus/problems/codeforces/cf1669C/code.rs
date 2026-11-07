impl Solution {
    pub fn can_make_same_parity(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut i: usize = 0;
        while i < n {
            if a[i] % 2 != a[0] % 2 {
                return false;
            }
            i = i + 2;
        }

        if n >= 2 {
            let mut j: usize = 1;
            while j < n {
                if a[j] % 2 != a[1] % 2 {
                    return false;
                }
                j = j + 2;
            }
        }

        true
    }
}
impl Solution {
    pub fn is_complementary_xor_possible(a: Vec<i64>, b: Vec<i64>) -> bool {
        let n = a.len();
        let first_xor = if a[0] == b[0] { 0i64 } else { 1i64 };
        let mut i: usize = 1;
        while i < n {
            let cur_xor = if a[i] == b[i] { 0i64 } else { 1i64 };
            if cur_xor != first_xor {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

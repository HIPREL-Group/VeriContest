impl Solution {
    pub fn minimum_stone_operations(a: Vec<i64>) -> Option<i64> {
        let n = a.len();
        if n == 3 {
            let m = a[1];
            if m % 2 == 1 {
                return None;
            }
            return Some(m / 2);
        }
        let mut all_one = true;
        let mut i: usize = 1;
        while i < n - 1 {
            if a[i] != 1 {
                all_one = false;
            }
            i = i + 1;
        }
        if all_one {
            return None;
        }
        let mut s: i64 = 0;
        let mut j: usize = 1;
        while j < n - 1 {
            s = s + (a[j] + 1) / 2;
            j = j + 1;
        }
        Some(s)
    }
}

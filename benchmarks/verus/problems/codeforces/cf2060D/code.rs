impl Solution {
    pub fn can_sort(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut cur: i64 = a[0];
        let mut i: usize = 0;
        while i < n - 1 {
            let next = a[i + 1];
            if cur > next {
                return false;
            }
            let new_cur = next - cur;
            cur = new_cur;
            i = i + 1;
        }
        true
    }
}

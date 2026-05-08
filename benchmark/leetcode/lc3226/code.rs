impl Solution {
    fn min_changes_rec(n: i32, k: i32) -> i32 {
        if n == 0 && k == 0 {
            0
        } else {
            let bn = n % 2;
            let bk = k % 2;
            if bk == 1 && bn == 0 {
                -1
            } else {
                let tail = Self::min_changes_rec(n / 2, k / 2);
                if tail < 0 {
                    -1
                } else if bn == 1 && bk == 0 {
                    tail + 1
                } else {
                    tail
                }
            }
        }
    }

    pub fn min_changes(n: i32, k: i32) -> i32 {
        Self::min_changes_rec(n, k)
    }
}

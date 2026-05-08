impl Solution {
    fn count_leq(mat: &Vec<Vec<i32>>, row: usize, col: usize, remaining: i32, cap: i32) -> i32 {
        if row >= mat.len() {
            if remaining >= 0 && cap >= 1 { return 1; } else { return 0; }
        }
        if col >= mat[row].len() {
            return 0;
        }
        if remaining < mat[row][col] {
            return 0;
        }
        let sub = Self::count_leq(mat, row + 1, 0, remaining - mat[row][col], cap);
        if sub >= cap {
            return cap;
        }
        let rest = Self::count_leq(mat, row, col + 1, remaining, cap - sub);
        let total = sub + rest;
        if total >= cap { cap } else { total }
    }

    pub fn kth_smallest(mat: Vec<Vec<i32>>, k: i32) -> i32 {
        let mut lo: i32 = 0;
        let mut hi: i32 = (mat.len() as i32) * 5000;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let cnt = Self::count_leq(&mat, 0, 0, mid, k);
            if cnt >= k {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo
    }
}

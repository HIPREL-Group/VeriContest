impl Solution {
    fn count_le_exec(m: i32, n: i32, x: i32) -> i64
    {
        let mut i: i32 = 1;
        let mut cnt: i64 = 0;
        while i <= m
        {
            let v = x / i;
            if v < n {
                cnt += v as i64;
            } else {
                cnt += n as i64;
            }
            i += 1;
        }
        cnt
    }

    pub fn find_kth_number(m: i32, n: i32, k: i32) -> i32
    {
        let mut lo: i64 = 1;
        let mut hi: i64 = m as i64 * n as i64;

        while lo < hi
        {
            let mid = lo + (hi - lo) / 2;
            let cnt = Self::count_le_exec(m, n, mid as i32);
            if cnt < k as i64 {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        lo as i32
    }
}

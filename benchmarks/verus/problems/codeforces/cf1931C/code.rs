impl Solution {
    pub fn min_cost_make_equal(a: Vec<i64>) -> i64 {
        let n: usize = a.len();

        let mut left: usize = 0;
        while left < n && a[left] == a[0] {
            left += 1;
        }

        let mut right: usize = 0;
        while right < n && a[n - 1 - right] == a[n - 1] {
            right += 1;
        }

        let mut ans: usize = if n - left <= n - right { n - left } else { n - right };
        if a[0] == a[n - 1] {
            let keep = if left + right <= n { left + right } else { n };
            ans = n - keep;
        }

        let out = ans as i64;
        out
    }
}

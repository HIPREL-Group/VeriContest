impl Solution {
    fn build_tables(n: usize, k: i64, a: &Vec<i64>) -> (Vec<i64>, Vec<i64>) {
        let half = n / 2;
        let size = (2 * k + 2) as usize;
        let mut diff: Vec<i64> = Vec::new();
        let mut exact: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < size {
            diff.push(0);
            exact.push(0);
            idx = idx + 1;
        }
        let mut i: usize = 0;
        while i < half {
            let ai = a[i];
            let aj = a[n - 1 - i];
            let lo = if ai < aj { ai } else { aj };
            let hi = if ai > aj { ai } else { aj };
            let left = (lo + 1) as usize;
            let right_plus_one = (hi + k + 1) as usize;
            let sum = (ai + aj) as usize;
            diff[left] = diff[left] + 1;
            diff[right_plus_one] = diff[right_plus_one] - 1;
            exact[sum] = exact[sum] + 1;
            i = i + 1;
        }
        (diff, exact)
    }

    pub fn constant_palindrome_sum(n: usize, k: i64, a: Vec<i64>) -> i64 {
        let tables = Solution::build_tables(n, k, &a);
        let diff = tables.0;
        let exact = tables.1;
        let mut ans = n as i64;
        let mut cover: i64 = 0;
        let mut x: usize = 2;
        let limit = (2 * k) as usize;
        while x <= limit {
            cover = cover + diff[x];
            let cost = n as i64 - cover - exact[x];
            if cost < ans {
                ans = cost;
            }
            x = x + 1;
        }
        ans
    }
}

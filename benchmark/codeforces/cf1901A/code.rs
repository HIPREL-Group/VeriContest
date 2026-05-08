impl Solution {
    pub fn min_tank_liters(x: i64, a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut ans: i64 = a[0];
        let mut i: usize = 0;
        let bound = n - 1;
        while i < bound {
            let d: i64 = a[i + 1] - a[i];
            if d > ans {
                ans = d;
            }
            i = i + 1;
        }
        let d2: i64 = 2 * (x - a[n - 1]);
        if d2 > ans {
            ans = d2;
        }
        ans
    }
}

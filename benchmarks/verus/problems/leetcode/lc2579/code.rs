impl Solution {
    pub fn colored_cells(n: i32) -> i64 {
        let mut ans: i128 = 1;
        let mut i: i128 = 1;

        while i < n as i128 {
            ans = ans + 4 * i;
            i = i + 1;
        }

        ans as i64
    }
}

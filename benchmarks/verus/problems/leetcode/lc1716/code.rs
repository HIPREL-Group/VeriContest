impl Solution {
    pub fn total_money(n: i32) -> i32 {
        let mut total: i32 = 0;
        let mut i: i32 = 1;
        while i <= n {
            let k = i - 1;
            total = total + k / 7 + k % 7 + 1;
            i = i + 1;
        }
        total
    }
}

impl Solution {
    pub fn concatenated_binary(n: i32) -> i32 {
        let modulo: i64 = 1_000_000_007;
        let mut ans: i64 = 0;
        let mut shift: i64 = 1;
        let mut i: i32 = 1;
        while i <= n {
            if i as i64 == shift {
                shift = shift * 2;
            }
            ans = (ans * shift + i as i64) % modulo;
            i += 1;
        }
        ans as i32
    }
}

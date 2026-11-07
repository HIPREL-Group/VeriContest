impl Solution {
    pub fn count_positions(n: i32, a: i32, b: i32) -> i32 {
        let min_pos = if a + 1 >= n - b { a + 1 } else { n - b };
        n - min_pos + 1
    }
}

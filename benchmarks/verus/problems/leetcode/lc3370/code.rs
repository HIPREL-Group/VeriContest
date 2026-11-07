impl Solution {
    pub fn smallest_number(n: i32) -> i32 {
        let target = n + 1;
        let mut p = 1;
        while p < target {
            p = p * 2;
        }
        p - 1
    }
}

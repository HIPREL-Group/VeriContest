impl Solution {
    pub fn is_three(n: i32) -> bool {
        let mut count: i32 = 0;
        let mut i: i32 = 1;
        while i <= n {
            if n % i == 0 {
                count = count + 1;
            }
            i = i + 1;
        }
        count == 3
    }
}

impl Solution {
    pub fn common_factors(a: i32, b: i32) -> i32 {
        let mut count: i32 = 0;
        let mut i: i32 = if a < b { a } else { b };
        while i > 0 {
            if a % i == 0 && b % i == 0 {
                count += 1;
            }
            i -= 1;
        }
        count
    }
}

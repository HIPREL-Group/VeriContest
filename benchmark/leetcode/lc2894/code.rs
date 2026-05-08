impl Solution {
    pub fn difference_of_sums(n: i32, m: i32) -> i32 {
        let mut diff: i32 = 0;
        let mut i: i32 = n;
        while i > 0 {
            if i % m == 0 {
                diff -= i;
            } else {
                diff += i;
            }
            i -= 1;
        }
        diff
    }
}

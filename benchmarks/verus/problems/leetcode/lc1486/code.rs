impl Solution {
    pub fn xor_operation(n: i32, start: i32) -> i32 {
        let mut ans: i32 = 0;
        let mut i: i32 = 0;
        while i < n {
            ans ^= start + 2 * i;
            i += 1;
        }
        ans
    }
}

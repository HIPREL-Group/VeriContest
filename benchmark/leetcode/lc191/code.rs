impl Solution {
    pub fn hamming_weight(n: i32) -> i32 {
        let mut acc: u32 = 0;
        let mut nmut = n as u32;
        while (nmut != 0) {
            acc += nmut % 2;
            nmut /= 2;
        }
        acc as i32
    }
}

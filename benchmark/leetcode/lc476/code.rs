impl Solution {
    pub fn find_complement(num: i32) -> i32 {
        let n = num as u32;
        let mut mask: u32 = 1;
        while mask <= n {
            mask = mask * 2;
        }
        (mask - 1 - n) as i32
    }
}

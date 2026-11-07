impl Solution {
    pub fn min_bit_flips(start: i32, goal: i32) -> i32 {
        let mut xor = (start ^ goal) as u32;
        let mut count: u32 = 0;
        while xor != 0 {
            count += xor % 2;
            xor /= 2;
        }
        count as i32
    }
}

impl Solution {
    pub fn hamming_distance(x: i32, y: i32) -> i32 {
        let mut xor = (x ^ y) as u32;
        let mut count: u32 = 0;
        while xor != 0 {
            count += xor % 2;
            xor /= 2;
        }
        count as i32
    }
}

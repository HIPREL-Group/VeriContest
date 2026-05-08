impl Solution {
    pub fn min_flips(a: i32, b: i32, c: i32) -> i32 {
        let mut flips: i32 = 0;
        let mut i: i32 = 0;
        while i < 31 {
            let bit_a = (a >> (i as u32)) & 1;
            let bit_b = (b >> (i as u32)) & 1;
            let bit_c = (c >> (i as u32)) & 1;
            if bit_c == 0 {
                flips = flips + bit_a + bit_b;
            } else {
                if bit_a == 0 && bit_b == 0 {
                    flips = flips + 1;
                }
            }
            i = i + 1;
        }
        flips
    }
}

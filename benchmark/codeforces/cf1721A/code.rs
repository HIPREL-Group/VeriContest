impl Solution {
    pub fn popcount_mask26(mask: u32) -> i32 {
        let mut d: i32 = 0;
        let mut k: u8 = 0;
        while k < 26 {
            let pre_d = d;
            let bit: i32 = if (mask >> k) & 1u32 == 0u32 {
                0
            } else {
                1
            };
            d = pre_d + bit;
            k = k + 1;
        }
        d
    }

    pub fn min_moves_to_uniform(a: u8, b: u8, c: u8, d: u8) -> i32 {
        let mask: u32 = (1u32 << a) | (1u32 << b) | (1u32 << c) | (1u32 << d);
        let distinct_i: i32 = Self::popcount_mask26(mask);
        let r = if distinct_i == 1 {
            0
        } else if distinct_i == 2 {
            1
        } else if distinct_i == 3 {
            2
        } else {
            3
        };
        r
    }
}

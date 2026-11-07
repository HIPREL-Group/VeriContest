impl Solution {
    pub fn find_complement_nonzero(num: i32) -> i32 {
        let n = num as u32;
        let mut mask: u32 = 1;
        while mask <= n {
            let old_mask = mask;
            mask = mask * 2;
        }
        (mask - 1 - n) as i32
    }

    pub fn bitwise_complement(n: i32) -> i32 {
        if n == 0 {
            return 1;
        }
        Self::find_complement_nonzero(n)
    }
}

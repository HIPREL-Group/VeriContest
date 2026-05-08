impl Solution {
    pub fn reverse_bits(n: i32) -> i32 {
        let (mut res, mut x) = (0i32, n);

        let mut i: u32 = 0;
        while i < 32 {
            let new_res = (res << 1) | (x & 1);
            let new_x = x >> 1;
            res = new_res;
            x = new_x;
            i += 1;
        }
        res
    }
}

impl Solution {
    fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64 {
        if modulus == 1 {
            return 0;
        }
        let mut result: u64 = 1;
        let mut base_pow: u64 = base % modulus;
        let mut i: u64 = 0;
        let mut mut_exp: u64 = exp;
        while mut_exp > 0 {
            if mut_exp % 2 != 0 {
                result = result * base_pow % modulus;
            }
            base_pow = base_pow * base_pow % modulus;
            mut_exp >>= 1;
            i += 1;
        }
        result
    }

    pub fn min_non_zero_product(p: i32) -> i32 {
        let modulus: u64 = 1_000_000_007;
        let mut val: u64 = 1;
        let mut j: i32 = 0;
        while j < p {
            val = val * 2;
            j = j + 1;
        }
        val = val - 1;
        let power: u64 = Self::mod_pow(val - 1, val / 2, modulus);
        ((power * (val % modulus)) % modulus) as i32
    }
}

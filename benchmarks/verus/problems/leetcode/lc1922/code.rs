impl Solution {
    pub const M: u64 = 1_000_000_007;
    
    fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64 {
        if modulus == 1 {
            return 0
        }
        let mut result = 1;
        let mut base_pow = base % modulus;
        let mut i: u64 = 0;
        let mut mut_exp = exp;
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

    pub fn count_good_numbers(n: i64) -> i32 {
        ((Self::mod_pow(4 * 5, n as u64 / 2, Self::M) * if n % 2 == 1 {
            5
        } else {
            1
        }) % Self::M) as i32
    }
}

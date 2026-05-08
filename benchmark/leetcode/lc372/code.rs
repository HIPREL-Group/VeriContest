impl Solution {
    pub const M: u64 = 1337;
    
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

    pub fn super_pow(a: i32, b: Vec<i32>) -> i32
    {
        let mut result: u64 = 1;
        let mut base_pow = a as u64 % Self::M;
        let mut i = 0;
        while i < b.len()
        {
            let mp = Self::mod_pow(base_pow, b[b.len() - i - 1] as u64, Self::M);
            result = result * mp % Self::M;
            base_pow = Self::mod_pow(base_pow, 10, Self::M);
            i += 1;
        }
        result as i32
    }
}

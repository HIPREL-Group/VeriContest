fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64 {
    if modulus == 1 {
        return 0;
    }
    let mut result: u64 = 1;
    let mut base_pow = base % modulus;
    let mut mut_exp = exp;
    while mut_exp > 0 {
        if mut_exp % 2 != 0 {
            result = result * base_pow % modulus;
        }
        base_pow = base_pow * base_pow % modulus;
        mut_exp >>= 1;
    }
    result
}

impl Solution {
    pub fn max_nice_divisors(prime_factors: i32) -> i32 {
        let modulus: u64 = 1_000_000_007;
        if prime_factors <= 3 {
            return prime_factors;
        }
        let pf = prime_factors as u64;
        let remainder = pf % 3;
        if remainder == 0 {
            let p = mod_pow(3, pf / 3, modulus);
            p as i32
        } else if remainder == 1 {
            let exp = (pf - 4) / 3;
            let p = mod_pow(3, exp, modulus);
            (4 * p % modulus) as i32
        } else {
            let exp = pf / 3;
            let p = mod_pow(3, exp, modulus);
            (2 * p % modulus) as i32
        }
    }
}

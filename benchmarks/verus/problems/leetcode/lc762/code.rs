impl Solution {
    pub fn is_small_prime(bits: i32) -> bool {
        bits == 2 || bits == 3 || bits == 5 || bits == 7 || bits == 11 || bits == 13 || bits == 17 || bits == 19
    }

    pub fn count_prime_set_bits(left: i32, right: i32) -> i32 {
        let mut result: i32 = 0;
        let mut num: i32 = left;
        while num <= right {
            let mut tmp: i32 = num;
            let mut bits: i32 = 0;
            while tmp > 0 {
                let bit = tmp % 2;
                bits = bits + bit;
                tmp = tmp / 2;
            }
            let prime = Self::is_small_prime(bits);
            let add: i32 = if prime { 1 } else { 0 };
            result = result + add;
            num = num + 1;
        }
        result
    }
}

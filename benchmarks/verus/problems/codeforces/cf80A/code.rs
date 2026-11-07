impl Solution {
    pub fn is_next_prime(n: u32, m: u32) -> bool {
        let mut x: u32 = n + 1;
        while x <= m {
            let mut prime: bool = true;
            let mut d: u32 = 2;
            while d < x {
                if x % d == 0 {
                    prime = false;
                }
                d = d + 1;
            }
            if prime {
                if x == m {
                    return true;
                } else {
                    return false;
                }
            }
            x = x + 1;
        }
        false
    }
}

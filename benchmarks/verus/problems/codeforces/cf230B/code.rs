impl Solution {
    fn floor_sqrt(x: u64) -> u64 {
        let mut lo = 1u64;
        let mut hi = 1_000_001u64;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid <= x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let r = lo - 1;
        r
    }

    fn is_prime_runtime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        let mut d = 2u64;
        while d <= n / d {
            if n % d == 0 {
                return false;
            }
            d += 1;
        }
        true
    }

    pub fn classify_t_primes(nums: Vec<u64>) -> Vec<bool> {
        let mut res = Vec::new();
        let mut i = 0usize;
        while i < nums.len() {
            let x = nums[i];
            let root = Self::floor_sqrt(x);
            let answer = if root * root == x {
                Self::is_prime_runtime(root)
            } else {
                false
            };
            res.push(answer);
            i += 1;
        }
        res
    }
}

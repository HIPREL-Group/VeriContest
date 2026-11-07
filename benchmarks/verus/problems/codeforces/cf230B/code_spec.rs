use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_prime(n: int) -> bool {
    2 <= n && forall|d: int| 2 <= d && d <= n / d ==> #[trigger] (n % d) != 0
}

pub open spec fn is_t_prime(x: int) -> bool {
    exists|p: int| 2 <= p && p * p == x && is_prime(p)
}

impl Solution {
    fn floor_sqrt(x: u64) -> (r: u64)
        requires
            1u64 <= x <= 1_000_000_000_000u64,
        ensures
            r <= 1_000_000u64,
            r * r <= x,
            x < (r + 1) * (r + 1),
    {
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

    fn is_prime_runtime(n: u64) -> (res: bool)
        requires
            n <= 1_000_000u64,
        ensures
            res == is_prime(n as int),
    {
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

    pub fn classify_t_primes(nums: Vec<u64>) -> (res: Vec<bool>)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1u64 <= #[trigger] nums[i] <= 1_000_000_000_000u64,
        ensures
            res.len() == nums.len(),
            forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] == is_t_prime(nums[i] as int),
    {
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

}

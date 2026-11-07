use std::io::{self, Read};

struct Solution;

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

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let mut nums = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        nums.push(tokens.next().expect("x").parse::<u64>().expect("valid u64"));
        i += 1;
    }
    let ans = Solution::classify_t_primes(nums);
    let mut out = String::new();
    i = 0;
    while i < ans.len() {
        if ans[i] {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
        i += 1;
    }
    print!("{}", out);
}

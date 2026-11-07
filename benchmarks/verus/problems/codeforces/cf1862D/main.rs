use std::io::{self, Read};

struct Solution;

impl Solution {
    fn tri_safe(x: u64) -> u64 {
        if x % 2 == 0 {
            (x / 2) * (x - 1)
        } else {
            x * ((x - 1) / 2)
        }
    }

    pub fn min_balls_for_types(n: u64) -> u64 {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo + 1 < hi {
            let mid = lo + (hi - lo) / 2;
            let tri_mid = Self::tri_safe(mid);
            if tri_mid <= n {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        let m = lo;
        let base = Self::tri_safe(m);
        let extra = n - base;
        let res = m + extra;
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let n: u64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::min_balls_for_types(n);
        println!("{}", ans);
        i = i + 1;
    }
}

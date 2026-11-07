use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn floor_sqrt_u64(x: u64) -> u64 {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
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

    pub fn min_bulbs_n(k: u64) -> u64 {
        let ub = k + 2_000_000_000u64 + 1000u64;
        let mut lo = 1u64;
        let mut hi = ub;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let s = Self::floor_sqrt_u64(mid);
            let cnt = mid - s;
            if cnt >= k {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let k: u64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::min_bulbs_n(k);
        println!("{}", ans);
        i = i + 1;
    }
}

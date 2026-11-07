use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn floor_sqrt_u64(m: u64) -> u64 {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid <= m {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let r = lo - 1;
        r
    }

    pub fn vasya_pythagorean_triples_count(n: u64) -> u64 {
        let m = 2 * n - 1;
        let k = Self::floor_sqrt_u64(m);
        if k < 3 {
            0
        } else {
            let res = (k + 1) / 2 - 1;
            res
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let n: u64 = it.next().unwrap().parse().unwrap();
        let answer = Solution::vasya_pythagorean_triples_count(n);
        println!("{}", answer);
        i += 1;
    }
}

use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn popcount_mask26(mask: u32) -> i32 {
        let mut d: i32 = 0;
        let mut k: u8 = 0;
        while k < 26 {
            let pre_d = d;
            let bit: i32 = if (mask >> k) & 1u32 == 0u32 {
                0
            } else {
                1
            };
            d = pre_d + bit;
            k = k + 1;
        }
        d
    }

    pub fn min_moves_to_uniform(a: u8, b: u8, c: u8, d: u8) -> i32 {
        let mask: u32 = (1u32 << a) | (1u32 << b) | (1u32 << c) | (1u32 << d);
        let distinct_i: i32 = Self::popcount_mask26(mask);
        let r = if distinct_i == 1 {
            0
        } else if distinct_i == 2 {
            1
        } else if distinct_i == 3 {
            2
        } else {
            3
        };
        r
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let row0: String = it.next().unwrap().to_string();
        let row1: String = it.next().unwrap().to_string();
        let b0: u8 = row0.as_bytes()[0];
        let b1: u8 = row0.as_bytes()[1];
        let b2: u8 = row1.as_bytes()[0];
        let b3: u8 = row1.as_bytes()[1];
        let a: u8 = b0 - b'a';
        let b: u8 = b1 - b'a';
        let c: u8 = b2 - b'a';
        let d: u8 = b3 - b'a';
        let ans = Solution::min_moves_to_uniform(a, b, c, d);
        println!("{}", ans);
        k = k + 1;
    }
}

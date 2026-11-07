use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_triangulation(n: u32) -> u64 {
        let mut sum: u64 = 0;
        let mut i: u32 = 2;
        while i < n {
            let i64v: u64 = i as u64;
            let term: u64 = i64v * (i64v + 1);
            sum = sum + term;
            i = i + 1;
        }
        sum
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let n: u32 = input.trim().parse().unwrap();
    let res = Solution::min_triangulation(n);
    println!("{}", res);
}

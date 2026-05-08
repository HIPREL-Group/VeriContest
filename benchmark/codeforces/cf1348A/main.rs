use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn phoenix_balance_min_diff(n: i32) -> i64 {
        let half = n / 2;
        let exp = half + 1;
        let mut p = 1i64;
        let mut k = 0i32;
        while k < exp {
            p = p * 2;
            k = k + 1;
        }
        p - 2
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut j: usize = 0;
    while j < t {
        let line = lines.next().unwrap().unwrap();
        let n: i32 = line.trim().parse().unwrap();
        println!("{}", Solution::phoenix_balance_min_diff(n));
        j = j + 1;
    }
}

use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn bun_chocolate_total(n: i64) -> i64 {
        let a = n as u128;
        let m = a * (a + 2);
        let v = m + 2;
        let r = v as i64;
        r
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let n: i64 = lines.next().unwrap().unwrap().trim().parse().unwrap();
        let ans = Solution::bun_chocolate_total(n);
        println!("{}", ans);
        i = i + 1;
    }
}

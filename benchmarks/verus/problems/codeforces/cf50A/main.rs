use std::io;

struct Solution;

impl Solution {
    pub fn max_dominoes(m: u32, n: u32) -> u32 {
        let mut area: u64 = 0;
        let mut i: u32 = 0;
        while i < m {
            area = area + (n as u64);
            i = i + 1;
        }
        let r = (area / 2) as u32;
        r
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read line");
    let parts: Vec<u32> = line
        .split_whitespace()
        .map(|s| s.parse().expect("integer"))
        .collect();
    let m = parts[0];
    let n = parts[1];
    println!("{}", Solution::max_dominoes(m, n));
}

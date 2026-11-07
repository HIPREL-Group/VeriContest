use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_pyramid_height(n: u64) -> u64 {
        let mut h: u64 = 0;
        let mut total: u64 = 0;
        let mut done: bool = false;
        while !done {
            if h >= 10001 {
                done = true;
            } else {
                let level = (h + 1) * (h + 2) / 2;
                if total + level > n {
                    done = true;
                } else {
                    total = total + level;
                    h = h + 1;
                }
            }
        }
        h
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: u64 = input.trim().parse().unwrap();
    let result = Solution::max_pyramid_height(n);
    writeln!(out, "{}", result).unwrap();
}

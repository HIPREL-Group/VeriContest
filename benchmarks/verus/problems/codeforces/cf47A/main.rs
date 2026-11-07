use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn is_triangular(n: u32) -> bool {
        let mut k: u32 = 1;
        while k <= n {
            if k * (k + 1) / 2 == n {
                return true;
            }
            k = k + 1;
        }
        false
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: u32 = input.trim().parse().unwrap();
    if Solution::is_triangular(n) {
        writeln!(out, "YES").unwrap();
    } else {
        writeln!(out, "NO").unwrap();
    }
}

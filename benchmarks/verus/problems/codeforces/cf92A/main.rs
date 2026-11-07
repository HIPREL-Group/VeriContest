use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn presenter_chips(n: u32, m: u32) -> u32 {
        let r_sum: u32 = n * (n + 1) / 2;
        let mut remaining: u32 = m % r_sum;
        let mut walrus: u32 = 1;
        while walrus <= n && remaining >= walrus {
            remaining = remaining - walrus;
            walrus = walrus + 1;
        }
        remaining
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: u32 = iter.next().unwrap().parse().unwrap();
    let m: u32 = iter.next().unwrap().parse().unwrap();
    writeln!(out, "{}", Solution::presenter_chips(n, m)).unwrap();
}

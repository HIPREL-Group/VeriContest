use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_monkeys(m: u64, a: u64, b: u64, c: u64) -> u64 {
        let row1: u64 = if m <= a { m } else { a };
        let row2: u64 = if m <= b { m } else { b };
        let remaining: u64 = 2 * m - row1 - row2;
        let extra: u64 = if c <= remaining { c } else { remaining };
        row1 + row2 + extra
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let m: u64 = iter.next().unwrap().parse().unwrap();
        let a: u64 = iter.next().unwrap().parse().unwrap();
        let b: u64 = iter.next().unwrap().parse().unwrap();
        let c: u64 = iter.next().unwrap().parse().unwrap();
        writeln!(out, "{}", Solution::max_monkeys(m, a, b, c)).unwrap();
    }
}

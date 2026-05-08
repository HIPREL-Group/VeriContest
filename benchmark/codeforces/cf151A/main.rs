use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_toasts(n: u64, k: u64, l: u64, c: u64, d: u64, p: u64, nl: u64, np: u64) -> u64 {
        let drink_toasts = (k * l) / nl;
        let lime_toasts = c * d;
        let salt_toasts = p / np;
        let m1 = if drink_toasts < lime_toasts { drink_toasts } else { lime_toasts };
        let m2 = if m1 < salt_toasts { m1 } else { salt_toasts };
        m2 / n
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: u64 = iter.next().unwrap().parse().unwrap();
    let k: u64 = iter.next().unwrap().parse().unwrap();
    let l: u64 = iter.next().unwrap().parse().unwrap();
    let c: u64 = iter.next().unwrap().parse().unwrap();
    let d: u64 = iter.next().unwrap().parse().unwrap();
    let p: u64 = iter.next().unwrap().parse().unwrap();
    let nl: u64 = iter.next().unwrap().parse().unwrap();
    let np: u64 = iter.next().unwrap().parse().unwrap();
    let result = Solution::max_toasts(n, k, l, c, d, p, nl, np);
    writeln!(out, "{}", result).unwrap();
}

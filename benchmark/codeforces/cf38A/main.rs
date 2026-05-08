use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn years_needed(n: usize, d: Vec<u32>, a: usize, b: usize) -> u32 {
        let mut sum: u32 = 0;
        let mut i: usize = a - 1;
        let lo: usize = a - 1;
        let hi: usize = b - 1;
        while i < hi {
            sum += d[i];
            i += 1;
        }
        sum
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let mut d: Vec<u32> = Vec::with_capacity(n - 1);
    for _ in 0..(n - 1) {
        d.push(iter.next().unwrap().parse().unwrap());
    }
    let a: usize = iter.next().unwrap().parse().unwrap();
    let b: usize = iter.next().unwrap().parse().unwrap();
    let result = Solution::years_needed(n, d, a, b);
    writeln!(out, "{}", result).unwrap();
}

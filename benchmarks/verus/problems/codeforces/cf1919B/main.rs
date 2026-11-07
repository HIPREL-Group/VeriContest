use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_penalty(plus_count: i64, minus_count: i64) -> i64 {
        if plus_count >= minus_count {
            plus_count - minus_count
        } else {
            minus_count - plus_count
        }
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
        let _n: usize = iter.next().unwrap().parse().unwrap();
        let s: &str = iter.next().unwrap();
        let mut plus: i64 = 0;
        let mut minus: i64 = 0;
        for b in s.bytes() {
            if b == b'+' { plus += 1; } else { minus += 1; }
        }
        let ans = Solution::min_penalty(plus, minus);
        writeln!(out, "{}", ans).unwrap();
    }
}

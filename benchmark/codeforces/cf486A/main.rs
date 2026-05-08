use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn calculating_function(n: i64) -> i64 {
        if n % 2 == 0 {
            n / 2
        } else {
            -((n + 1) / 2)
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: i64 = input.trim().parse().unwrap();
    let result = Solution::calculating_function(n);
    writeln!(out, "{}", result).unwrap();
}

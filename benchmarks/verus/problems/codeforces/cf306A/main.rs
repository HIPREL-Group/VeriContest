use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn distribute(n: u32, m: u32) -> Vec<u32> {
        let q = n / m;
        let r = n % m;
        let big_count = r;
        let small_count = m - r;
        let mut result: Vec<u32> = Vec::new();
        let mut i: u32 = 0;
        while i < small_count {
            result.push(q);
            i = i + 1;
        }
        let mut j: u32 = 0;
        while j < big_count {
            result.push(q + 1);
            j = j + 1;
        }
        result
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
    let res = Solution::distribute(n, m);
    let parts: Vec<String> = res.iter().map(|v| v.to_string()).collect();
    writeln!(out, "{}", parts.join(" ")).unwrap();
}

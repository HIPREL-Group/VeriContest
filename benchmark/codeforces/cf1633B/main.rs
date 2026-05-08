use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn minority_count(s: &Vec<u8>) -> u64 {
        let n = s.len();
        let mut c0: u64 = 0;
        let mut c1: u64 = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 0u8 {
                c0 = c0 + 1;
            } else {
                c1 = c1 + 1;
            }
            i = i + 1;
        }
        if c0 == 0 || c1 == 0 {
            0
        } else if c0 == c1 {
            c0 - 1
        } else if c0 < c1 {
            c0
        } else {
            c1
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
        let s = iter.next().unwrap();
        let v: Vec<u8> = s.bytes().map(|b| if b == b'0' { 0u8 } else { 1u8 }).collect();
        let res = Solution::minority_count(&v);
        writeln!(out, "{}", res).unwrap();
    }
}

use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn colourblind_match(n: usize, row1: Vec<u8>, row2: Vec<u8>) -> bool {
        let mut i: usize = 0;
        while i < n {
            let a = row1[i];
            let b = row2[i];
            let na = if a == 1u8 || a == 2u8 { 1u8 } else { a };
            let nb = if b == 1u8 || b == 2u8 { 1u8 } else { b };
            if na != nb {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn parse_row(s: &str) -> Vec<u8> {
    s.bytes()
        .map(|b| match b {
            b'R' => 0u8,
            b'G' => 1u8,
            b'B' => 2u8,
            _ => 0u8,
        })
        .collect()
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let n: usize = iter.next().unwrap().parse().unwrap();
        let s1 = iter.next().unwrap();
        let s2 = iter.next().unwrap();
        let row1 = parse_row(s1);
        let row2 = parse_row(s2);
        let res = Solution::colourblind_match(n, row1, row2);
        if res {
            writeln!(out, "YES").unwrap();
        } else {
            writeln!(out, "NO").unwrap();
        }
    }
}

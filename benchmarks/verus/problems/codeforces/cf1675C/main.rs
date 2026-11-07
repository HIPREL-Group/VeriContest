use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn count_suspects(s: Vec<u8>) -> usize {
        let n = s.len();
        let mut last_one: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 1u8 {
                last_one = i;
            }
            i += 1;
        }
        let mut first_zero: usize = n - 1;
        let mut j: usize = 0;
        let mut found_zero: bool = false;
        while j < n {
            if s[j] == 0u8 && !found_zero {
                first_zero = j;
                found_zero = true;
            }
            j += 1;
        }
        first_zero - last_one + 1
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
        let s_str = iter.next().unwrap();
        let v: Vec<u8> = s_str.bytes().map(|b| match b {
            b'0' => 0u8,
            b'1' => 1u8,
            b'?' => 2u8,
            _ => 2u8,
        }).collect();
        let res = Solution::count_suspects(v);
        writeln!(out, "{}", res).unwrap();
    }
}

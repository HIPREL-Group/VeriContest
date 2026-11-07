use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_days(s: Vec<u8>, f: Vec<u8>) -> usize {
        let mut remove_count: usize = 0;
        let mut add_count: usize = 0;
        let mut i: usize = 0;
        while i < s.len() {
            if s[i] == 1 && f[i] == 0 {
                remove_count = remove_count + 1;
            } else if s[i] == 0 && f[i] == 1 {
                add_count = add_count + 1;
            }
            i = i + 1;
        }
        if remove_count > add_count {
            remove_count
        } else {
            add_count
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut it = input.split_ascii_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let s_str = it.next().unwrap();
        let f_str = it.next().unwrap();
        let s: Vec<u8> = s_str.bytes().map(|b| if b == b'1' { 1u8 } else { 0u8 }).collect();
        let f: Vec<u8> = f_str.bytes().map(|b| if b == b'1' { 1u8 } else { 0u8 }).collect();
        let _ = n;
        let ans = Solution::min_days(s, f);
        writeln!(out, "{}", ans).unwrap();
        tc = tc + 1;
    }
}

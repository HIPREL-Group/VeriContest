use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_seconds(left: Vec<u8>, right: Vec<u8>, n: usize) -> usize {
        let mut l_open: usize = 0;
        let mut r_open: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if left[i] == 1u8 {
                l_open = l_open + 1;
            }
            if right[i] == 1u8 {
                r_open = r_open + 1;
            }
            i = i + 1;
        }
        let l_min: usize = if l_open <= n - l_open { l_open } else { n - l_open };
        let r_min: usize = if r_open <= n - r_open { r_open } else { n - r_open };
        l_min + r_min
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let mut left: Vec<u8> = Vec::with_capacity(n);
    let mut right: Vec<u8> = Vec::with_capacity(n);
    for _ in 0..n {
        let l: u8 = iter.next().unwrap().parse().unwrap();
        let r: u8 = iter.next().unwrap().parse().unwrap();
        left.push(l);
        right.push(r);
    }
    let ans = Solution::min_seconds(left, right, n);
    writeln!(out, "{}", ans).unwrap();
}

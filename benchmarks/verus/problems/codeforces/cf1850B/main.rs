use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn find_winner(a: Vec<u32>, b: Vec<u32>, n: usize) -> usize {
        let mut best_idx: usize = 0;
        let mut best_b: u32 = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n {
            if a[i] <= 10 {
                if !found || b[i] > best_b {
                    best_idx = i;
                    best_b = b[i];
                    found = true;
                }
            }
            i += 1;
        }
        best_idx + 1
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
        let n: usize = iter.next().unwrap().parse().unwrap();
        let mut a: Vec<u32> = Vec::with_capacity(n);
        let mut b: Vec<u32> = Vec::with_capacity(n);
        for _ in 0..n {
            let ai: u32 = iter.next().unwrap().parse().unwrap();
            let bi: u32 = iter.next().unwrap().parse().unwrap();
            a.push(ai);
            b.push(bi);
        }
        let result = Solution::find_winner(a, b, n);
        writeln!(out, "{}", result).unwrap();
    }
}

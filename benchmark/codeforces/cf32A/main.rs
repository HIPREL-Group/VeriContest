use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn count_recon_pairs(n: usize, d: i64, heights: Vec<i64>) -> u64 {
        let mut count: u64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < i {
                let a = heights[i];
                let b = heights[j];
                let diff: i64 = if a >= b { a - b } else { b - a };
                if diff <= d {
                    count = count + 2;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let d: i64 = iter.next().unwrap().parse().unwrap();
    let mut heights: Vec<i64> = Vec::with_capacity(n);
    for _ in 0..n {
        heights.push(iter.next().unwrap().parse().unwrap());
    }
    let result = Solution::count_recon_pairs(n, d, heights);
    writeln!(out, "{}", result).unwrap();
}

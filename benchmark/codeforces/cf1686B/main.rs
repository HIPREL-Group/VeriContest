use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_odd_subarrays(n: usize, p: Vec<i64>) -> usize {
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i + 1 < n {
            if p[i] > p[i + 1] {
                count += 1;
                i += 2;
            } else {
                i += 1;
            }
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
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let n: usize = iter.next().unwrap().parse().unwrap();
        let mut p: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            p.push(iter.next().unwrap().parse().unwrap());
        }
        let res = Solution::max_odd_subarrays(n, p);
        writeln!(out, "{}", res).unwrap();
    }
}

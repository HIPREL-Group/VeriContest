use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_moves_to_equalize(n: usize, a: Vec<u64>, b: Vec<u64>) -> u64 {
        let mut ma: u64 = a[0];
        let mut mb: u64 = b[0];
        let mut i: usize = 1;
        while i < n {
            if a[i] < ma { ma = a[i]; }
            if b[i] < mb { mb = b[i]; }
            i += 1;
        }
        let mut total: u64 = 0;
        let mut j: usize = 0;
        while j < n {
            let da = a[j] - ma;
            let db = b[j] - mb;
            let m = if da >= db { da } else { db };
            total = total + m;
            j += 1;
        }
        total
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
        let mut a: Vec<u64> = Vec::with_capacity(n);
        for _ in 0..n {
            a.push(iter.next().unwrap().parse().unwrap());
        }
        let mut b: Vec<u64> = Vec::with_capacity(n);
        for _ in 0..n {
            b.push(iter.next().unwrap().parse().unwrap());
        }
        let ans = Solution::min_moves_to_equalize(n, a, b);
        writeln!(out, "{}", ans).unwrap();
    }
}

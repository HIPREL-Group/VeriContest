use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn answer_queries(a: Vec<i8>, qls: Vec<usize>, qrs: Vec<usize>) -> Vec<u8> {
        let n = a.len();
        let m = qls.len();
        let mut pos: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1i8 {
                pos = pos + 1;
            }
            i = i + 1;
        }
        let neg = n - pos;
        let mut out: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        while k < m {
            let l = qls[k];
            let r = qrs[k];
            let len = r - l + 1;
            let half = len / 2;
            if len % 2 == 0 && half <= pos && half <= neg {
                out.push(1u8);
            } else {
                out.push(0u8);
            }
            k = k + 1;
        }
        out
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let m: usize = iter.next().unwrap().parse().unwrap();
    let mut a: Vec<i8> = Vec::with_capacity(n);
    for _ in 0..n {
        let v: i8 = iter.next().unwrap().parse().unwrap();
        a.push(v);
    }
    let mut qls: Vec<usize> = Vec::with_capacity(m);
    let mut qrs: Vec<usize> = Vec::with_capacity(m);
    for _ in 0..m {
        let l: usize = iter.next().unwrap().parse().unwrap();
        let r: usize = iter.next().unwrap().parse().unwrap();
        qls.push(l);
        qrs.push(r);
    }
    let ans = Solution::answer_queries(a, qls, qrs);
    for v in &ans {
        writeln!(out, "{}", v).unwrap();
    }
}

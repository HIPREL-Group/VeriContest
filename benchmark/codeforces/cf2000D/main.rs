use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_score(a: Vec<i64>, s: Vec<u8>) -> i64 {
        let n = a.len();
        let mut prefix: Vec<i64> = Vec::with_capacity(n + 1);
        prefix.push(0);
        let mut i: usize = 0;
        while i < n {
            let next = prefix[i] + a[i];
            prefix.push(next);
            i = i + 1;
        }
        let mut total: i64 = 0;
        let mut lo: usize = 0;
        let mut hi: usize = n;
        let mut keep_going: bool = true;
        while keep_going {
            while lo < hi && s[lo] != 1 {
                lo = lo + 1;
            }
            while lo < hi && s[hi - 1] != 2 {
                hi = hi - 1;
            }
            if lo + 1 < hi {
                total = total + prefix[hi] - prefix[lo];
                lo = lo + 1;
                hi = hi - 1;
            } else {
                keep_going = false;
            }
        }
        total
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
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let s_str = it.next().unwrap();
        let s: Vec<u8> = s_str.bytes().map(|b| match b {
            b'L' => 1u8,
            b'R' => 2u8,
            _ => 0u8,
        }).collect();
        let _ = n;
        let ans = Solution::max_score(a, s);
        writeln!(out, "{}", ans).unwrap();
        tc = tc + 1;
    }
}

use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn vlad_beautiful(a: Vec<u32>, n: usize) -> bool {
        let mut min_even: u64 = u64::MAX;
        let mut min_odd: u64 = u64::MAX;
        let mut min_even_idx: usize = 0;
        let mut min_odd_idx: usize = 0;
        let mut i: usize = 0;
        while i < n {
            let v = a[i] as u64;
            if a[i] % 2 == 0 {
                if v < min_even {
                    min_even = v;
                    min_even_idx = i;
                }
            } else {
                if v < min_odd {
                    min_odd = v;
                    min_odd_idx = i;
                }
            }
            i += 1;
        }
        if min_even == u64::MAX {
            true
        } else if min_odd == u64::MAX {
            true
        } else {
            let res = min_odd < min_even;
            res
        }
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
        for _ in 0..n {
            let v: u32 = iter.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let result = Solution::vlad_beautiful(a, n);
        writeln!(out, "{}", if result { "YES" } else { "NO" }).unwrap();
    }
}

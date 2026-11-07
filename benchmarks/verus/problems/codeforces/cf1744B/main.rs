use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn even_odd_sums(a: Vec<u32>, n: usize, qtypes: Vec<u32>, qxs: Vec<u32>, q: usize) -> Vec<i64> {
        let mut sum: i64 = 0;
        let mut ce: i64 = 0;
        let mut co: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            sum += a[i] as i64;
            if a[i] % 2 == 0 {
                ce += 1;
            } else {
                co += 1;
            }
            i += 1;
        }
        let mut result: Vec<i64> = Vec::with_capacity(q);
        let mut k: usize = 0;
        while k < q {
            let t = qtypes[k];
            let x = qxs[k] as i64;
            if t == 0 {
                sum += ce * x;
                if x % 2 == 1 {
                    co += ce;
                    ce = 0;
                }
            } else {
                sum += co * x;
                if x % 2 == 1 {
                    ce += co;
                    co = 0;
                }
            }
            result.push(sum);
            k += 1;
        }
        result
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
        let q: usize = iter.next().unwrap().parse().unwrap();
        let mut a: Vec<u32> = Vec::with_capacity(n);
        for _ in 0..n {
            a.push(iter.next().unwrap().parse().unwrap());
        }
        let mut qtypes: Vec<u32> = Vec::with_capacity(q);
        let mut qxs: Vec<u32> = Vec::with_capacity(q);
        for _ in 0..q {
            qtypes.push(iter.next().unwrap().parse().unwrap());
            qxs.push(iter.next().unwrap().parse().unwrap());
        }
        let sums = Solution::even_odd_sums(a, n, qtypes, qxs, q);
        for s in sums {
            writeln!(out, "{}", s).unwrap();
        }
    }
}

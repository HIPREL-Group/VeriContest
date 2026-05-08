use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn top_card(n: usize, a: Vec<i64>, m: usize, b: Vec<i64>) -> i64 {
        let n_i64 = n as i64;
        let mut idx: i64 = 0;
        let mut i: usize = 0;
        while i < m {
            let bi = b[i];
            let s_old: i64 = idx + bi;
            let new_idx: i64 = if s_old >= n_i64 { s_old - n_i64 } else { s_old };
            idx = new_idx;
            i = i + 1;
        }
        a[idx as usize]
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
        let mut a: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            a.push(iter.next().unwrap().parse().unwrap());
        }
        let m: usize = iter.next().unwrap().parse().unwrap();
        let mut b: Vec<i64> = Vec::with_capacity(m);
        for _ in 0..m {
            b.push(iter.next().unwrap().parse().unwrap());
        }
        let res = Solution::top_card(n, a, m, b);
        writeln!(out, "{}", res).unwrap();
    }
}

use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn can_shower(s: i64, m: i64, l: Vec<i64>, r: Vec<i64>) -> bool {
        let n = l.len();
        let mut max_gap: i64 = l[0];
        let mut i: usize = 0;
        while i < n {
            let end_pos: i64 = if i + 1 == n { m } else { l[i + 1] };
            let gap = end_pos - r[i];
            if gap > max_gap {
                max_gap = gap;
            }
            i = i + 1;
        }
        max_gap >= s
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
        let s: i64 = it.next().unwrap().parse().unwrap();
        let m: i64 = it.next().unwrap().parse().unwrap();
        let mut l: Vec<i64> = Vec::with_capacity(n);
        let mut r: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            l.push(it.next().unwrap().parse().unwrap());
            r.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::can_shower(s, m, l, r);
        writeln!(out, "{}", if ans { "YES" } else { "NO" }).unwrap();
        tc = tc + 1;
    }
}

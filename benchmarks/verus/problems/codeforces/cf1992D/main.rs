use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn can_cross(a: Vec<u8>, m: usize, k: i64) -> bool {
        let n = a.len();
        let inf: i64 = 300_000;
        let mut dp: Vec<i64> = Vec::with_capacity(n + 2);
        dp.push(0);
        let mut p: usize = 1;
        while p <= n + 1 {
            let val = if p <= n && a[p - 1] == 1 {
                inf
            } else {
                let lo: usize = if p > m { p - m } else { 0 };
                let mut best = inf;
                let mut jj: usize = p;
                while jj > lo {
                    jj = jj - 1;
                    let djv = dp[jj];
                    if djv < inf {
                        let valid = if jj == 0 || jj == n + 1 || (1 <= jj && jj <= n && a[jj - 1] == 2) {
                            jj + 1 <= p && p <= jj + m
                        } else if 1 <= jj && jj <= n && a[jj - 1] == 0 {
                            p == jj + 1
                        } else {
                            false
                        };
                        if valid {
                            let cost: i64 = if p >= 1 && p <= n && a[p - 1] == 0 { 1 } else { 0 };
                            let cand = djv + cost;
                            if cand < best {
                                best = cand;
                            }
                        }
                    }
                }
                best
            };
            dp.push(val);
            p = p + 1;
        }
        dp[n + 1] < inf && dp[n + 1] <= k
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
        let m: usize = it.next().unwrap().parse().unwrap();
        let k: i64 = it.next().unwrap().parse().unwrap();
        let s_str = it.next().unwrap();
        let a: Vec<u8> = s_str.bytes().map(|b| match b {
            b'W' => 0u8,
            b'C' => 1u8,
            b'L' => 2u8,
            _ => 0u8,
        }).collect();
        let _ = n;
        let ans = Solution::can_cross(a, m, k);
        writeln!(out, "{}", if ans { "YES" } else { "NO" }).unwrap();
        tc = tc + 1;
    }
}

use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn min_swaps(n: usize, a: Vec<u32>) -> i64 {
        let mut odd_at_even: i64 = 0;
        let mut even_at_odd: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if i % 2 == 0 && a[i] % 2 == 1 {
                odd_at_even += 1;
            } else if i % 2 == 1 && a[i] % 2 == 0 {
                even_at_odd += 1;
            }
            i += 1;
        }
        if odd_at_even == even_at_odd {
            odd_at_even
        } else {
            -1
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
            a.push(iter.next().unwrap().parse().unwrap());
        }
        let ans = Solution::min_swaps(n, a);
        writeln!(out, "{}", ans).unwrap();
    }
}

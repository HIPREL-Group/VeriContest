use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn count_good_prefixes_fn(a: Vec<u64>) -> usize {
        let mut sum: u64 = 0;
        let mut max_val: u64 = 0;
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < a.len() {
            let ai = a[i];
            sum = sum + ai;
            if ai > max_val {
                max_val = ai;
            }
            if 2 * max_val == sum {
                count = count + 1;
            }
            i = i + 1;
        }
        count
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
        let mut a: Vec<u64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::count_good_prefixes_fn(a);
        writeln!(out, "{}", ans).unwrap();
        tc = tc + 1;
    }
}

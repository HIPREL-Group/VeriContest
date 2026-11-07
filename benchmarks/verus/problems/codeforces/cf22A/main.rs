use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn second_min(a: Vec<i32>, n: usize) -> Option<i32> {
        let mut min_val: i32 = a[0];
        let mut i: usize = 1;
        while i < n {
            if a[i] < min_val {
                min_val = a[i];
            }
            i = i + 1;
        }
        let mut found: bool = false;
        let mut second: i32 = 0i32;
        let mut k: usize = 0;
        while k < n {
            if a[k] > min_val {
                if !found || a[k] < second {
                    second = a[k];
                    found = true;
                }
            }
            k = k + 1;
        }
        if found {
            Some(second)
        } else {
            None
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let v: i32 = iter.next().unwrap().parse().unwrap();
        a.push(v);
    }
    match Solution::second_min(a, n) {
        Some(v) => writeln!(out, "{}", v).unwrap(),
        None => writeln!(out, "NO").unwrap(),
    }
}

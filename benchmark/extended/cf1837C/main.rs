use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn best_binary_string(s: Vec<i64>) -> Vec<i64> {
        let n = s.len();
        let mut result: Vec<i64> = Vec::new();
        let mut last: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] != 2 {
                last = s[i];
            }
            result.push(last);
            i = i + 1;
        }
        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let pat = it.next().unwrap();
        let mut s: Vec<i64> = Vec::new();
        let bytes = pat.as_bytes();
        let mut j: usize = 0;
        while j < bytes.len() {
            if bytes[j] == b'0' {
                s.push(0);
            } else if bytes[j] == b'1' {
                s.push(1);
            } else {
                s.push(2);
            }
            j = j + 1;
        }
        let result = Solution::best_binary_string(s);
        let mut out = String::new();
        let mut k: usize = 0;
        while k < result.len() {
            if result[k] == 0 {
                out.push('0');
            } else {
                out.push('1');
            }
            k = k + 1;
        }
        println!("{}", out);
        tc = tc + 1;
    }
}

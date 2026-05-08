use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn restore_array(n: usize, b: Vec<i64>) -> Vec<i64> {
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if i == 0 {
                a.push(b[0]);
            } else if i < n - 1 {
                if b[i - 1] <= b[i] {
                    a.push(b[i - 1]);
                } else {
                    a.push(b[i]);
                }
            } else {
                a.push(b[n - 2]);
            }
            i = i + 1;
        }
        a
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().unwrap().parse().unwrap();
    let mut tc = 0;
    while tc < t {
        let n: usize = tokens.next().unwrap().parse().unwrap();
        let mut b: Vec<i64> = Vec::with_capacity(n - 1);
        let mut j = 0;
        while j < n - 1 {
            b.push(tokens.next().unwrap().parse().unwrap());
            j = j + 1;
        }
        let result = Solution::restore_array(n, b);
        let mut out = String::new();
        let mut j = 0;
        while j < n {
            if j > 0 {
                out.push(' ');
            }
            out.push_str(&result[j].to_string());
            j = j + 1;
        }
        println!("{}", out);
        tc = tc + 1;
    }
}

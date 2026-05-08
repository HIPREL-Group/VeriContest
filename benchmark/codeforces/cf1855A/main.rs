use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_swaps(p: Vec<i32>) -> i32 {
        let n = p.len();
        let mut c: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if p[i] == (i + 1) as i32 {
                c = c + 1;
            }
            i = i + 1;
        }
        (c + 1) / 2
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case: usize = 0;
    while case < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");
        let mut p: Vec<i32> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            p.push(tokens.next().expect("p").parse().expect("valid i32"));
            idx = idx + 1;
        }
        println!("{}", Solution::min_swaps(p));
        case = case + 1;
    }
}

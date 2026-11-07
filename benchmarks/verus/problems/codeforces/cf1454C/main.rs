use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_ops(a: Vec<i64>) -> u64 {
        let n = a.len();
        let mut segments: Vec<u64> = Vec::new();
        let mut init: usize = 0;
        while init <= n {
            segments.push(0);
            init = init + 1;
        }
        let mut i: usize = 0;
        while i < n {
            if i == 0 || a[i] != a[i - 1] {
                let idx = a[i] as usize;
                segments[idx] = segments[idx] + 1;
            }
            i = i + 1;
        }

        let mut best: u64 = (n + 1) as u64;
        let mut x: usize = 1;
        while x <= n {
            if segments[x] > 0 {
                let mut ops = segments[x] + 1;
                if a[0] == x as i64 {
                    ops = ops - 1;
                }
                if a[n - 1] == x as i64 {
                    ops = ops - 1;
                }
                if ops < best {
                    best = ops;
                }
            }
            x = x + 1;
        }
        best
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
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            a.push(tokens.next().expect("element").parse().expect("valid i64"));
            idx = idx + 1;
        }
        let answer = Solution::min_ops(a);
        println!("{}", answer);
        case = case + 1;
    }
}

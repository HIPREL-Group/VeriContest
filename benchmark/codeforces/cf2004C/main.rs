use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn optimal_score(a: Vec<i64>, k: i64) -> u64 {
        let n = a.len();
        let mut i: usize = 0;
        let mut cur_k: i64 = k;
        let mut answer: u64 = 0;

        while i < n {
            if i + 1 == n {
                answer = answer + a[i] as u64;
                i = i + 1;
            } else {
                let diff = a[i] - a[i + 1];
                if cur_k >= diff {
                    cur_k = cur_k - diff;
                } else {
                    answer = answer + (diff - cur_k) as u64;
                    cur_k = 0;
                }
                i = i + 2;
            }
        }

        answer
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    if let Some(t_str) = tokens.next() {
        let t: usize = t_str.parse().expect("t");
        for _ in 0..t {
            if let Some(n_str) = tokens.next() {
                let n: usize = n_str.parse().expect("n");
                let k: i64 = tokens.next().expect("k").parse().expect("k");
                let mut a: Vec<i64> = Vec::with_capacity(n);
                let mut i = 0;
                while i < n {
                    a.push(tokens.next().expect("a").parse::<i64>().expect("a"));
                    i += 1;
                }
                a.sort_unstable_by(|x: &i64, y: &i64| y.cmp(x));
                println!("{}", Solution::optimal_score(a, k));
            }
        }
    }
}

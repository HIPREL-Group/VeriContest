use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn best_shift(a: Vec<i64>) -> (usize, usize) {
        let n = a.len();
        let mut best_l: usize = 0;
        let mut best_r: usize = 0;
        let mut best_delta: i64 = 0;
        let mut l: usize = 0;
        while l < n {
            let mut cur_delta: i64 = 0;
            let mut r: usize = l + 1;
            while r < n {
                if a[r] < a[l] {
                    cur_delta = cur_delta - 1;
                } else if a[r] > a[l] {
                    cur_delta = cur_delta + 1;
                }
                if cur_delta < best_delta {
                    best_delta = cur_delta;
                    best_l = l;
                    best_r = r;
                }
                r = r + 1;
            }
            l = l + 1;
        }
        (best_l, best_r)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let t: usize = it.next().expect("t").parse().expect("valid t");
    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().expect("n").parse().expect("valid n");
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().expect("a").parse().expect("valid a"));
            i = i + 1;
        }
        let ans = Solution::best_shift(a);
        println!("{} {}", ans.0 + 1, ans.1 + 1);
        case_idx = case_idx + 1;
    }
}

use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn good_pair_indices(a: Vec<i64>) -> (i64, i64) {
        let n = a.len();
        let mut min_i = 0usize;
        let mut max_i = 0usize;
        let mut i = 1usize;
        while i < n {
            if a[i] < a[min_i] {
                min_i = i;
            }
            if a[i] > a[max_i] {
                max_i = i;
            }
            i = i + 1;
        }
        ((min_i + 1) as i64, (max_i + 1) as i64)
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut tc = 0usize;
    while tc < t {
        let _n_line = lines.next().unwrap().unwrap();
        let a_line = lines.next().unwrap().unwrap();
        let a: Vec<i64> = a_line
            .split_whitespace()
            .map(|x| x.parse().unwrap())
            .collect();
        let (i, j) = Solution::good_pair_indices(a);
        println!("{} {}", i, j);
        tc = tc + 1;
    }
}

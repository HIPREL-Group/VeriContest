use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_advancing(scores: Vec<i32>, k: usize) -> usize {
        let threshold = scores[k - 1];
        let mut count = 0usize;
        let mut i = 0usize;
        while i < scores.len() {
            if scores[i] >= threshold && scores[i] > 0 {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: usize = it.next().unwrap().parse().unwrap();
    let mut scores: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        scores.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let answer = Solution::count_advancing(scores, k);
    println!("{}", answer);
}

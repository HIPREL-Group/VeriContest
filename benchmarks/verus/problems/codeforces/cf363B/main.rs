use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_sum_window_start(heights: Vec<i32>, k: usize) -> usize {
        let n = heights.len();
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < k {
            let idx = i;
            sum = sum + heights[idx] as i64;
            i = idx + 1;
        }
        let mut best_sum = sum;
        let mut best_start: usize = 0;
        let mut start: usize = 1;
        while start + k <= n {
            let prev_start = start;
            let prev_best_sum = best_sum;
            let prev_best_start = best_start;
            sum = sum - heights[prev_start - 1] as i64 + heights[prev_start + k - 1] as i64;
            if sum < best_sum {
                best_sum = sum;
                best_start = prev_start;
            }
            start = prev_start + 1;
        }
        best_start + 1
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: usize = it.next().unwrap().parse().unwrap();
    let mut heights: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        heights.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let answer = Solution::min_sum_window_start(heights, k);
    println!("{}", answer);
}

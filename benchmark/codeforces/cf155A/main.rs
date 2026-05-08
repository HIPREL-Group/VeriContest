use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_amazing_performances(points: Vec<i32>, n: usize) -> usize {
        if n <= 1 {
            return 0;
        }
        let mut count = 0usize;
        let mut min_so_far = points[0];
        let mut max_so_far = points[0];
        let mut i = 1usize;
        while i < n {
            if points[i] > max_so_far || points[i] < min_so_far {
                count += 1;
            }
            if points[i] > max_so_far {
                max_so_far = points[i];
            }
            if points[i] < min_so_far {
                min_so_far = points[i];
            }
            i += 1;
        }
        count
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let points: Vec<i32> = line
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ans = Solution::count_amazing_performances(points, n);
    println!("{}", ans);
}

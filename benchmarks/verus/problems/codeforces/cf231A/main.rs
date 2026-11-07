use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_teams_implement(grid: Vec<i32>, n: usize) -> usize {
        let mut count = 0usize;
        let mut i = 0usize;
        while i < n {
            let idx = 3 * i;
            let s = (grid[idx] as i64) + (grid[idx + 1] as i64) + (grid[idx + 2] as i64);
            if s >= 2 {
                count += 1;
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
    let mut grid: Vec<i32> = Vec::with_capacity(3 * n);
    for _ in 0..n {
        let line = lines.next().unwrap().unwrap();
        let parts: Vec<i32> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        grid.push(parts[0]);
        grid.push(parts[1]);
        grid.push(parts[2]);
    }
    let ans = Solution::count_teams_implement(grid, n);
    println!("{}", ans);
}

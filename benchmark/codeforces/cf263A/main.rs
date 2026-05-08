use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_moves_beautiful_matrix(grid: Vec<i32>) -> i32 {
        let mut r = 0usize;
        let mut c = 0usize;
        while r < 5 {
            c = 0;
            while c < 5 {
                if grid[5 * r + c] == 1 {
                    let dr = if (r as i32) >= 2 { (r as i32) - 2 } else { 2 - (r as i32) };
                    let dc = if (c as i32) >= 2 { (c as i32) - 2 } else { 2 - (c as i32) };
                    return dr + dc;
                }
                c += 1;
            }
            r += 1;
        }
        0
    }
}

fn main() {
    let stdin = io::stdin();
    let mut grid: Vec<i32> = Vec::new();
    for _ in 0..5 {
        let mut line = String::new();
        stdin.lock().read_line(&mut line).expect("read line");
        for s in line.split_whitespace() {
            grid.push(s.parse::<i32>().expect("integer"));
        }
    }
    let ans = Solution::min_moves_beautiful_matrix(grid);
    println!("{}", ans);
}

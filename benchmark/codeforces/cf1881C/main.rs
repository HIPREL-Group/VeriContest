use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_ops_perfect_square(n: usize, grid: Vec<i64>) -> i64 {
        let half = n / 2;
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < half {
            let mut j: usize = 0;
            while j < half {
                let v0 = grid[i * n + j];
                let v1 = grid[j * n + (n - 1 - i)];
                let v2 = grid[(n - 1 - i) * n + (n - 1 - j)];
                let v3 = grid[(n - 1 - j) * n + i];
                let mut m = v0;
                if v1 > m {
                    m = v1;
                }
                if v2 > m {
                    m = v2;
                }
                if v3 > m {
                    m = v3;
                }
                total = total + (m - v0) + (m - v1) + (m - v2) + (m - v3);
                j = j + 1;
            }
            i = i + 1;
        }
        total
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().expect("t line");
    let t: usize = t_line.expect("read t").trim().parse().expect("parse t");
    for _ in 0..t {
        let n_line = lines.next().expect("n line");
        let n: usize = n_line.expect("read n").trim().parse().expect("parse n");
        let mut grid: Vec<i64> = Vec::new();
        for _ in 0..n {
            let row = lines.next().expect("row").expect("read row");
            let row = row.trim();
            for ch in row.chars() {
                grid.push((ch as u8 - b'a') as i64);
            }
        }
        let ans = Solution::min_ops_perfect_square(n, grid);
        println!("{}", ans);
    }
}

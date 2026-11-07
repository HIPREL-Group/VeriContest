use std::io::{self, BufRead, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn is_valley(n: usize, a: Vec<i64>) -> i64 {
        let mut count: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let block_start = i;
            while i < n && a[i] == a[block_start] {
                i += 1;
            }
            let block_end = i - 1;
            let left_ok = block_start == 0 || a[block_start - 1] > a[block_start];
            let right_ok = block_end == n - 1 || a[block_end] < a[block_end + 1];
            if left_ok && right_ok {
                count += 1;
            }
        }
        count
    }
}

fn main() {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut lines = stdin.lock().lines();

    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    for _ in 0..t {
        let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
        let a: Vec<i64> = lines.next().unwrap().unwrap().split_whitespace()
            .map(|s| s.parse().unwrap()).collect();
        let count = Solution::is_valley(n, a);
        if count == 1 {
            writeln!(out, "YES").unwrap();
        } else {
            writeln!(out, "NO").unwrap();
        }
    }
}

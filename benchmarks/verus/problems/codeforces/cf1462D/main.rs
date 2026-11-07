use std::io::{self, BufRead, Write, BufWriter};

struct Solution;

impl Solution {
    fn compute_sum(n: usize, a: &Vec<i64>) -> i64 {
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total += a[i];
            i += 1;
        }
        total
    }

    fn check_partition(n: usize, a: &Vec<i64>, g: usize, total: i64) -> bool {
        let target = total / (g as i64);
        let mut seg_sum: i64 = 0;
        let mut count: usize = 0;
        let mut j: usize = 0;
        let mut ok = true;
        while j < n {
            if ok {
                seg_sum += a[j];
            }
            j += 1;
            if ok && seg_sum == target {
                count += 1;
                seg_sum = 0;
            } else if ok && seg_sum > target {
                ok = false;
            }
        }
        if ok && count == g && seg_sum == 0 {
            true
        } else {
            false
        }
    }

    pub fn min_operations(n: usize, a: Vec<i64>) -> i64 {
        let total = Solution::compute_sum(n, &a);
        let mut best_k: usize = 1;
        let mut g: usize = n;
        while g >= 1 {
            if total % (g as i64) == 0 && total >= g as i64 {
                let ok = Solution::check_partition(n, &a, g, total);
                if ok {
                    best_k = g;
                    return (n as i64) - (best_k as i64);
                }
            }
            g -= 1;
        }
        (n as i64) - (best_k as i64)
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
        let ans = Solution::min_operations(n, a);
        writeln!(out, "{}", ans).unwrap();
    }
}

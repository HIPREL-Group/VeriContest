use std::io::{self, BufRead, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn co_growing(n: usize, x: Vec<u32>) -> Vec<u32> {
        let mut y: Vec<u32> = Vec::new();
        let mut z: u32 = x[0];
        let y0 = z ^ x[0];
        y.push(y0);
        let mut i: usize = 1;
        while i < n {
            let old_z = z;
            z = z | x[i];
            let yi = z ^ x[i];
            y.push(yi);
            i += 1;
        }
        y
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
        let x: Vec<u32> = lines.next().unwrap().unwrap().split_whitespace()
            .map(|s| s.parse().unwrap()).collect();
        let y = Solution::co_growing(n, x);
        let parts: Vec<String> = y.iter().map(|v| v.to_string()).collect();
        writeln!(out, "{}", parts.join(" ")).unwrap();
    }
}

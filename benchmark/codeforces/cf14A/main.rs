use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn bounding_box(grid: &Vec<Vec<u8>>, n: usize, m: usize) -> (usize, usize, usize, usize) {
        let mut min_r: usize = n;
        let mut max_r: usize = 0;
        let mut min_c: usize = m;
        let mut max_c: usize = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < m {
                if grid[i][j] == 1u8 {
                    if !found {
                        min_r = i;
                        max_r = i;
                        min_c = j;
                        max_c = j;
                        found = true;
                    } else {
                        if i < min_r { min_r = i; }
                        if i > max_r { max_r = i; }
                        if j < min_c { min_c = j; }
                        if j > max_c { max_c = j; }
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        (min_r, max_r, min_c, max_c)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let m: usize = iter.next().unwrap().parse().unwrap();
    let mut grid: Vec<Vec<u8>> = Vec::with_capacity(n);
    let mut raw_grid: Vec<Vec<u8>> = Vec::with_capacity(n);
    for _ in 0..n {
        let s = iter.next().unwrap();
        let row: Vec<u8> = s.bytes().map(|b| if b == b'*' { 1u8 } else { 0u8 }).collect();
        let raw_row: Vec<u8> = s.bytes().collect();
        grid.push(row);
        raw_grid.push(raw_row);
    }
    let (min_r, max_r, min_c, max_c) = Solution::bounding_box(&grid, n, m);
    for r in min_r..=max_r {
        for c in min_c..=max_c {
            out.write_all(&[raw_grid[r][c]]).unwrap();
        }
        writeln!(out).unwrap();
    }
}

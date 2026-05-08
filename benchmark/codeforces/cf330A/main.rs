use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn cakeminator(r: usize, c: usize, grid: Vec<Vec<u8>>) -> u64 {
        let mut clean_rows: u64 = 0;
        let mut i: usize = 0;
        while i < r {
            let mut clean: bool = true;
            let mut j: usize = 0;
            while j < c {
                if grid[i][j] == 1 {
                    clean = false;
                }
                j = j + 1;
            }
            if clean {
                clean_rows = clean_rows + 1;
            }
            i = i + 1;
        }
        let mut clean_cols: u64 = 0;
        let mut j: usize = 0;
        while j < c {
            let mut clean: bool = true;
            let mut i: usize = 0;
            while i < r {
                if grid[i][j] == 1 {
                    clean = false;
                }
                i = i + 1;
            }
            if clean {
                clean_cols = clean_cols + 1;
            }
            j = j + 1;
        }
        clean_rows * (c as u64) + clean_cols * (r as u64) - clean_rows * clean_cols
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let r: usize = iter.next().unwrap().parse().unwrap();
    let c: usize = iter.next().unwrap().parse().unwrap();
    let mut grid: Vec<Vec<u8>> = Vec::with_capacity(r);
    for _ in 0..r {
        let s: String = iter.next().unwrap().to_string();
        let mut row: Vec<u8> = Vec::with_capacity(c);
        for ch in s.chars() {
            row.push(if ch == 'S' { 1u8 } else { 0u8 });
        }
        grid.push(row);
    }
    writeln!(
        out,
        "{}",
        Solution::cakeminator(r, c, grid)
    )
    .unwrap();
}

use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn red_last(grid: Vec<u8>) -> bool {
        let mut found: bool = false;
        let mut r: usize = 0;
        while r < 8 {
            let mut all_r: bool = true;
            let mut c: usize = 0;
            while c < 8 {
                if grid[r * 8 + c] != 0 {
                    all_r = false;
                }
                c += 1;
            }
            if all_r {
                found = true;
            }
            r += 1;
        }
        found
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        
        let mut grid: Vec<u8> = Vec::with_capacity(64);
        for _ in 0..8 {
            let s: &str = iter.next().unwrap();
            for ch in s.chars() {
                let v = match ch {
                    'R' => 0u8,
                    'B' => 1u8,
                    _ => 2u8,
                };
                grid.push(v);
            }
        }
        let result = Solution::red_last(grid);
        writeln!(out, "{}", if result { "R" } else { "B" }).unwrap();
    }
}

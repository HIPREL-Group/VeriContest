use std::io::{self, Read};

pub struct Solution;

impl Solution {
    pub fn manhattan_circle_center(grid: Vec<Vec<i32>>) -> (i32, i32) {
        let n = grid.len();
        let m = grid[0].len();

        let mut found: bool = false;
        let mut min_r: usize = 0usize;
        let mut max_r: usize = 0usize;
        let mut min_c: usize = 0usize;
        let mut max_c: usize = 0usize;

        let mut i: usize = 0usize;
        while i < n {
            let mut j: usize = 0usize;
            while j < m {
                if grid[i][j] == 1 {
                    if !found {
                        found = true;
                        min_r = i;
                        max_r = i;
                        min_c = j;
                        max_c = j;
                    } else {
                        if i < min_r {
                            min_r = i;
                        }
                        if i > max_r {
                            max_r = i;
                        }
                        if j < min_c {
                            min_c = j;
                        }
                        if j > max_c {
                            max_c = j;
                        }
                    }
                }
                j += 1;
            }
            i += 1;
        }

        let center_r = ((min_r + max_r) / 2 + 1) as i32;
        let center_c = ((min_c + max_c) / 2 + 1) as i32;
        (center_r, center_c)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    let mut case_idx = 0usize;
    while case_idx < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let _m: usize = it.next().unwrap().parse().unwrap();

        let mut grid: Vec<Vec<i32>> = Vec::with_capacity(n);
        let mut i = 0usize;
        while i < n {
            let row = it.next().unwrap().as_bytes();
            let mut vals: Vec<i32> = Vec::with_capacity(row.len());
            let mut j = 0usize;
            while j < row.len() {
                vals.push(if row[j] == b'#' { 1 } else { 0 });
                j += 1;
            }
            grid.push(vals);
            i += 1;
        }

        let (r, c) = Solution::manhattan_circle_center(grid);
        out.push_str(&format!("{} {}\n", r, c));
        case_idx += 1;
    }

    print!("{}", out);
}

use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn is_symmetric(grid: Vec<u8>) -> bool {
        grid[0] == grid[8] && grid[1] == grid[7] && grid[2] == grid[6] && grid[3] == grid[5]
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut grid: Vec<u8> = Vec::with_capacity(9);
    for line in input.lines() {
        let trimmed = line.trim_end();
        for c in trimmed.chars() {
            if c == 'X' {
                grid.push(1u8);
            } else if c == '.' {
                grid.push(0u8);
            }
            if grid.len() == 9 {
                break;
            }
        }
        if grid.len() == 9 {
            break;
        }
    }
    while grid.len() < 9 {
        grid.push(0u8);
    }
    if Solution::is_symmetric(grid) {
        println!("YES");
    } else {
        println!("NO");
    }
}

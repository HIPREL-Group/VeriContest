use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn minutes_before_new_year_one(h: i32, m: i32) -> i32 {
        let result = (1440i64 - 60i64 * (h as i64) - (m as i64)) as i32;
        result
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut j: usize = 0;
    while j < t {
        let line = lines.next().unwrap().unwrap();
        let mut it = line.split_whitespace();
        let h: i32 = it.next().unwrap().parse().unwrap();
        let m: i32 = it.next().unwrap().parse().unwrap();
        println!("{}", Solution::minutes_before_new_year_one(h, m));
        j = j + 1;
    }
}

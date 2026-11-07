use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn has_triangle(sticks: Vec<i32>) -> bool {
        let mut found = false;
        let mut i = 0usize;
        while i < 4 {
            let mut j = 0usize;
            while j < 4 {
                let mut k = 0usize;
                while k < 4 {
                    if i != j && i != k && j != k {
                        let a = sticks[i] as i64;
                        let b = sticks[j] as i64;
                        let c = sticks[k] as i64;
                        if a + b > c && a + c > b && b + c > a {
                            found = true;
                        }
                    }
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        found
    }
}

fn main() {
    let stdin = io::stdin();
    let line = stdin.lock().lines().next().unwrap().unwrap();
    let parts: Vec<i32> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
    let sticks = vec![parts[0], parts[1], parts[2], parts[3]];
    let has_tri = Solution::has_triangle(sticks.clone());
    let has_seg = Solution::has_segment(sticks);
    if has_tri {
        println!("TRIANGLE");
    } else if has_seg {
        println!("SEGMENT");
    } else {
        println!("IMPOSSIBLE");
    }
}

impl Solution {
    pub fn has_segment(sticks: Vec<i32>) -> bool {
        let mut i = 0usize;
        while i < 4 {
            let mut j = 0usize;
            while j < 4 {
                let mut k = 0usize;
                while k < 4 {
                    if i != j && i != k && j != k {
                        let a = sticks[i] as i64;
                        let b = sticks[j] as i64;
                        let c = sticks[k] as i64;
                        if a + b == c || a + c == b || b + c == a {
                            return true;
                        }
                    }
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        false
    }
}
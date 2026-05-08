use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn can_make_beautiful(a: i32, b: i32, c: i32, d: i32) -> bool {
        (a < b && c < d && a < c && b < d)
            || (c < a && d < b && c < d && a < b)
            || (d < c && b < a && d < b && c < a)
            || (b < d && a < c && b < a && d < c)
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            let mut tc: usize = 0;
            while tc < t {
                if let Some(Ok(row1)) = lines.next() {
                    if let Some(Ok(row2)) = lines.next() {
                        let r1: Vec<i32> = row1.split_whitespace().map(|x| x.parse().unwrap()).collect();
                        let r2: Vec<i32> = row2.split_whitespace().map(|x| x.parse().unwrap()).collect();
                        if r1.len() >= 2 && r2.len() >= 2 {
                            let a = r1[0];
                            let b = r1[1];
                            let c = r2[0];
                            let d = r2[1];
                            if Solution::can_make_beautiful(a, b, c, d) {
                                println!("YES");
                            } else {
                                println!("NO");
                            }
                        }
                    }
                }
                tc += 1;
            }
        }
    }
}

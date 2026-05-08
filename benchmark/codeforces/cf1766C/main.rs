use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_paint_wall(m: usize, row0: Vec<i64>, row1: Vec<i64>) -> bool {
        let mut dp0: bool;
        let mut dp1: bool;
        if row0[0] == 1 && row1[0] == 0 {
            dp0 = true;
            dp1 = false;
        } else if row0[0] == 0 && row1[0] == 1 {
            dp0 = false;
            dp1 = true;
        } else {
            dp0 = true;
            dp1 = true;
        }
        let mut j: usize = 1;
        while j < m {
            let new_dp0: bool;
            let new_dp1: bool;
            if row0[j] == 1 && row1[j] == 0 {
                new_dp0 = dp0;
                new_dp1 = false;
            } else if row0[j] == 0 && row1[j] == 1 {
                new_dp0 = false;
                new_dp1 = dp1;
            } else {
                new_dp0 = dp1;
                new_dp1 = dp0;
            }
            dp0 = new_dp0;
            dp1 = new_dp1;
            j = j + 1;
        }
        dp0 || dp1
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut iter = input.split_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let m: usize = iter.next().unwrap().parse().unwrap();
        let s0: &str = iter.next().unwrap();
        let s1: &str = iter.next().unwrap();
        let b0 = s0.as_bytes();
        let b1 = s1.as_bytes();
        let mut row0: Vec<i64> = Vec::with_capacity(m);
        let mut row1: Vec<i64> = Vec::with_capacity(m);
        let mut j: usize = 0;
        while j < m {
            if b0[j] == b'B' { row0.push(1); } else { row0.push(0); }
            if b1[j] == b'B' { row1.push(1); } else { row1.push(0); }
            j = j + 1;
        }
        if Solution::can_paint_wall(m, row0, row1) {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}

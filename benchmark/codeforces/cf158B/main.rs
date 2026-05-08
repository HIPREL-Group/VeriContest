use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_taxis(c1: i32, c2: i32, c3: i32, c4: i32) -> i32 {
        let mut c1_rem = c1;
        let mut ans = c4;
        ans += c3;
        if c1_rem > c3 {
            c1_rem = c1_rem - c3;
        } else {
            c1_rem = 0;
        }
        ans += (c2 + 1) / 2;
        if c2 % 2 == 1 {
            if c1_rem > 2 {
                c1_rem = c1_rem - 2;
            } else {
                c1_rem = 0;
            }
        }
        ans += (c1_rem + 3) / 4;
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut c1: i32 = 0;
    let mut c2: i32 = 0;
    let mut c3: i32 = 0;
    let mut c4: i32 = 0;
    let mut i: usize = 0;
    while i < n {
        let s: i32 = it.next().unwrap().parse().unwrap();
        if s == 1 {
            c1 += 1;
        } else if s == 2 {
            c2 += 1;
        } else if s == 3 {
            c3 += 1;
        } else {
            c4 += 1;
        }
        i += 1;
    }
    let answer = Solution::min_taxis(c1, c2, c3, c4);
    println!("{}", answer);
}

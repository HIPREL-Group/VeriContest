use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_catch_coin(x: i32, y: i32) -> bool {
        let _ = x;
        y >= -1
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < n {
        let x: i32 = it.next().unwrap().parse().unwrap();
        let y: i32 = it.next().unwrap().parse().unwrap();
        if Solution::can_catch_coin(x, y) {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}

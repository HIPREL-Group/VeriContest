use std::io;

struct Solution;

impl Solution {
    pub fn can_split_even(w: u32) -> bool {
        w >= 4 && w % 2 == 0
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read line");
    let w: u32 = line.trim().parse().expect("integer");
    if Solution::can_split_even(w) {
        println!("YES");
    } else {
        println!("NO");
    }
}

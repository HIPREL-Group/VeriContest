use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn first_wins(a: i64, b: i64, c: i64) -> bool {
        if a > b {
            true
        } else if a < b {
            false
        } else {
            (c % 2) == 1
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case: usize = 0;
    while case < t {
        let a: i64 = tokens.next().expect("a").parse().expect("valid a");
        let b: i64 = tokens.next().expect("b").parse().expect("valid b");
        let c: i64 = tokens.next().expect("c").parse().expect("valid c");
        if Solution::first_wins(a, b, c) {
            println!("First");
        } else {
            println!("Second");
        }
        case = case + 1;
    }
}

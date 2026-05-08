use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn one_is_sum_of_others(a: i64, b: i64, c: i64) -> bool {
        a == b + c || b == a + c || c == a + b
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        let c: i64 = it.next().unwrap().parse().unwrap();
        if Solution::one_is_sum_of_others(a, b, c) {
            println!("YES");
        } else {
            println!("NO");
        }
        k = k + 1;
    }
}

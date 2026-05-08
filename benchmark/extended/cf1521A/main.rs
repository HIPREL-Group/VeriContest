use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn construct_numbers(a: i64, b: i64) -> (bool, i64, i64, i64) {
        if b == 1 {
            (false, 0, 0, 0)
        } else {
            let x = a;
            let y = a * b;
            let z = a * (b + 1);
            (true, x, y, z)
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        let (ok, x, y, z) = Solution::construct_numbers(a, b);
        if ok {
            println!("YES");
            println!("{} {} {}", x, y, z);
        } else {
            println!("NO");
        }
        case_idx = case_idx + 1;
    }
}

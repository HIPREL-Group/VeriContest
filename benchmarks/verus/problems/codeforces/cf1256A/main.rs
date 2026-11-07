use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn payment_without_change(a: i64, b: i64, n: i64, S: i64) -> bool {
        let x = if a < S / n {
            a
        } else {
            S / n
        };
        let rem = S - x * n;
        rem <= b
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
        let n: i64 = it.next().unwrap().parse().unwrap();
        let s: i64 = it.next().unwrap().parse().unwrap();
        let ok = Solution::payment_without_change(a, b, n, s);
        if ok {
            println!("YES");
        } else {
            println!("NO");
        }
        k = k + 1;
    }
}

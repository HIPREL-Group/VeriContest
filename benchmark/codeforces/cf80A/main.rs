use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn is_next_prime(n: u32, m: u32) -> bool {
        let mut x: u32 = n + 1;
        while x <= m {
            let mut prime: bool = true;
            let mut d: u32 = 2;
            while d < x {
                if x % d == 0 {
                    prime = false;
                }
                d = d + 1;
            }
            if prime {
                if x == m {
                    return true;
                } else {
                    return false;
                }
            }
            x = x + 1;
        }
        false
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: u32 = iter.next().unwrap().parse().unwrap();
    let m: u32 = iter.next().unwrap().parse().unwrap();
    writeln!(
        out,
        "{}",
        if Solution::is_next_prime(n, m) { "YES" } else { "NO" }
    )
    .unwrap();
}

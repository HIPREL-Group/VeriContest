use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn freedom_possible(n: i64, m: i64) -> bool {
        if n == 1 {
            return true;
        }
        if m >= n {
            return false;
        }
        let mut d: i64 = 2;
        while d * d <= n {
            if n % d == 0 {
                return d > m;
            }
            d = d + 1;
        }
        true
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let m: i64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::freedom_possible(n, m);
        if ans {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
    }

    print!("{}", out);
}

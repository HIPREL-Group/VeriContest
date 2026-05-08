use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_square(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut total: i64 = 0;
        let mut k: usize = 0;
        while k < n {
            total = total + a[k];
            k = k + 1;
        }
        let mut lo: i64 = 0;
        let mut hi: i64 = 15_000_000;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid < total {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo * lo == total
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case: usize = 0;
    while case < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            a.push(tokens.next().expect("element").parse().expect("valid i64"));
            idx = idx + 1;
        }
        if Solution::can_square(a) {
            println!("YES");
        } else {
            println!("NO");
        }
        case = case + 1;
    }
}

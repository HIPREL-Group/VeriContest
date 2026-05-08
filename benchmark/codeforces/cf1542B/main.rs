use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn n_in_generated_set(n: i64, a: i64, b: i64) -> bool {
        if a == 1 {
            (n - 1) % b == 0
        } else {
            let mut pow: i64 = 1;
            while pow <= n {
                if (n - pow) % b == 0 {
                    return true;
                }
                if pow > n / a {
                    return false;
                }
                pow = pow * a;
            }
            false
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::n_in_generated_set(n, a, b);
        if ans {
            println!("Yes");
        } else {
            println!("No");
        }
        k = k + 1;
    }
}

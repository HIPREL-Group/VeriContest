use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn almost_equal(n: usize) -> Vec<i64> {
        if n % 2 == 0 {
            return Vec::new();
        }
        let mut res: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if i % 2 == 0 {
                res.push((2 * i + 1) as i64);
            } else {
                res.push((2 * i + 2) as i64);
            }
            i = i + 1;
        }
        i = 0;
        while i < n {
            if i % 2 == 0 {
                res.push((2 * i + 2) as i64);
            } else {
                res.push((2 * i + 1) as i64);
            }
            i = i + 1;
        }
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let n: usize = input.trim().parse().unwrap();
    let res = Solution::almost_equal(n);
    if res.is_empty() {
        println!("NO");
    } else {
        println!("YES");
        let parts: Vec<String> = res.iter().map(|x| x.to_string()).collect();
        println!("{}", parts.join(" "));
    }
}

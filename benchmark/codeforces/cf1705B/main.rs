use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_operations(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut ans: i64 = 0;
        let mut started: bool = false;
        let mut i: usize = 0;
        while i + 1 < n {
            let ai = a[i];
            if ai > 0 {
                ans = ans + ai;
                started = true;
            } else if started {
                ans = ans + 1;
            }
            i = i + 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }
        let ans = Solution::min_operations(a);
        println!("{}", ans);
        tc = tc + 1;
    }
}

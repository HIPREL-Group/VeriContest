use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_tank_liters(x: i64, a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut ans: i64 = a[0];
        let mut i: usize = 0;
        let bound = n - 1;
        while i < bound {
            let d: i64 = a[i + 1] - a[i];
            if d > ans {
                ans = d;
            }
            i = i + 1;
        }
        let d2: i64 = 2 * (x - a[n - 1]);
        if d2 > ans {
            ans = d2;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let x: i64 = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }
        let ans = Solution::min_tank_liters(x, a);
        println!("{}", ans);
        k = k + 1;
    }
}

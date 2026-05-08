use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_product_one_increment(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut best: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut p: i64 = 1;
            let mut j: usize = 0;
            while j < n {
                if j == i {
                    p = p * (a[j] + 1);
                } else {
                    p = p * a[j];
                }
                j = j + 1;
            }
            if p > best {
                best = p;
            }
            i = i + 1;
        }
        best
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
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }
        let ans = Solution::max_product_one_increment(a);
        println!("{}", ans);
        k = k + 1;
    }
}

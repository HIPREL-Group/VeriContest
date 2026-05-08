use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn maximal_continuous_rest(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut i: usize = 0;
        let total: usize = 2 * n;
        while i < total {
            let idx: usize = i % n;
            if a[idx] == 1 {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
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
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        let x: i32 = it.next().unwrap().parse().unwrap();
        a.push(x);
        j = j + 1;
    }
    let answer = Solution::maximal_continuous_rest(a);
    println!("{}", answer);
}

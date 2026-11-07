use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn battle_for_survive(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut s = 0i64;
        let mut i = 0usize;
        while i < n {
            s = s + a[i];
            i = i + 1;
        }
        s - 2 * a[n - 2]
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k = 0usize;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            j = j + 1;
        }
        let ans = Solution::battle_for_survive(a);
        println!("{}", ans);
        k = k + 1;
    }
}

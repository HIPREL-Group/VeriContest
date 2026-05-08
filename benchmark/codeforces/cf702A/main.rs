use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_increasing_subarray_len(n: usize, a: Vec<i64>) -> usize {
        let mut best = 1usize;
        let mut cur = 1usize;
        let mut i = 1usize;
        while i < n {
            if a[i] > a[i - 1] {
                cur = cur + 1;
            } else {
                cur = 1;
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
    let mut a: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    let ans = Solution::max_increasing_subarray_len(n, a);
    println!("{}", ans);
}

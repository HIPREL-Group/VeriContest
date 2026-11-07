use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_max_difficulty(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut min_result = 10000;
        let mut k: usize = 1;
        while k < n - 1 {
            let mut max_gap = 0;
            let mut i: usize = 0;
            while i < n - 1 {
                let gap = if i == k - 1 {
                    a[k + 1] - a[k - 1]
                } else {
                    a[i + 1] - a[i]
                };
                if gap > max_gap {
                    max_gap = gap;
                }
                if i == k - 1 {
                    i = k + 1;
                } else {
                    i = i + 1;
                }
            }
            if max_gap < min_result {
                min_result = max_gap;
            }
            k = k + 1;
        }
        min_result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }
    let answer = Solution::min_max_difficulty(a);
    println!("{}", answer);
}

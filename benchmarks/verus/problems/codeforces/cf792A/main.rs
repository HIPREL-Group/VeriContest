use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_gap_and_count(n: usize, a: Vec<i64>) -> (i64, i64) {
        let mut min_d = a[1] - a[0];
        let mut cnt: i64 = 1;
        let mut k: usize = 1;
        while k < n - 1 {
            let d = a[k + 1] - a[k];
            if d < min_d {
                min_d = d;
                cnt = 1;
            } else if d == min_d {
                cnt = cnt + 1;
            }
            k = k + 1;
        }
        (min_d, cnt)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    a.sort_unstable();
    let (x, y) = Solution::min_gap_and_count(n, a);
    println!("{} {}", x, y);
}

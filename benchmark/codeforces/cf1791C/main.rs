use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn shortest_original(n: usize, s: Vec<i64>) -> usize {
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right {
            if s[left] + s[right] != 1 {
                return right - left + 1;
            }
            left += 1;
            right -= 1;
        }
        if left > right {
            0
        } else {
            right - left + 1
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let line: &str = it.next().unwrap();
        let bytes = line.as_bytes();
        let mut s: Vec<i64> = Vec::with_capacity(n);
        let mut j: usize = 0;
        while j < n {
            s.push((bytes[j] - b'0') as i64);
            j += 1;
        }
        let answer = Solution::shortest_original(n, s);
        println!("{}", answer);
        i += 1;
    }
}

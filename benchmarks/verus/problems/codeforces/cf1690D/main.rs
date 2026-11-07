use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_recolors(n: usize, k: usize, s: Vec<i64>) -> usize {
        let mut cur: i64 = 0;
        let mut j: usize = 0;
        while j < k {
            cur = cur + s[j];
            j += 1;
        }

        let mut best: i64 = cur;
        let mut left: usize = 0;

        while left + k < n {
            let next = cur - s[left] + s[left + k];
            cur = next;
            left += 1;
            if cur < best {
                best = cur;
            }
        }

        best as usize
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let k: usize = it.next().unwrap().parse().unwrap();
        let stripe = it.next().unwrap().as_bytes();

        let mut s: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            if stripe[i] == b'W' {
                s.push(1);
            } else {
                s.push(0);
            }
            i += 1;
        }

        let ans = Solution::min_recolors(n, k, s);
        println!("{}", ans);
        case_id += 1;
    }
}
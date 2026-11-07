use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn meme_pair_count(a_max: i64, b_max: i64) -> i64 {
        let mut ans: i64 = 0;
        if 9 <= b_max {
            ans = ans + a_max;
        }
        if 99 <= b_max {
            ans = ans + a_max;
        }
        if 999 <= b_max {
            ans = ans + a_max;
        }
        if 9_999 <= b_max {
            ans = ans + a_max;
        }
        if 99_999 <= b_max {
            ans = ans + a_max;
        }
        if 999_999 <= b_max {
            ans = ans + a_max;
        }
        if 9_999_999 <= b_max {
            ans = ans + a_max;
        }
        if 99_999_999 <= b_max {
            ans = ans + a_max;
        }
        if 999_999_999 <= b_max {
            ans = ans + a_max;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let a_max: i64 = it.next().unwrap().parse().unwrap();
        let b_max: i64 = it.next().unwrap().parse().unwrap();
        let answer = Solution::meme_pair_count(a_max, b_max);
        println!("{}", answer);
        i += 1;
    }
}

use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_friends_for_equal_candies(a: Vec<i64>) -> i32 {
        let n = a.len();
        let ni = n as i64;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + a[i];
            i = i + 1;
        }
        if sum % ni != 0 {
            return -1;
        }
        let t = sum / ni;
        let mut cnt: i32 = 0;
        i = 0;
        while i < n {
            if a[i] > t {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
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
            let x: i64 = it.next().unwrap().parse().unwrap();
            a.push(x);
            i = i + 1;
        }
        let ans = Solution::min_friends_for_equal_candies(a);
        println!("{}", ans);
        k = k + 1;
    }
}

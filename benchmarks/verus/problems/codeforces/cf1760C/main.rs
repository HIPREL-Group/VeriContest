use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn advantages(s: Vec<i64>) -> Vec<i64> {
        let n = s.len();
        let mut max1: i64 = s[0];
        let mut idx1: usize = 0;
        let mut max2: i64 = s[1];
        let mut idx2: usize = 1;

        if max2 > max1 {
            let tv = max1;
            let ti = idx1;
            max1 = max2;
            idx1 = idx2;
            max2 = tv;
            idx2 = ti;
        }

        let mut t: usize = 2;
        while t < n {
            if s[t] > max1 {
                max2 = max1;
                idx2 = idx1;
                max1 = s[t];
                idx1 = t;
            } else if s[t] > max2 {
                max2 = s[t];
                idx2 = t;
            }
            t = t + 1;
        }

        let mut result: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            let best: i64;
            if i == idx1 {
                best = max2;
            } else {
                best = max1;
            }

            result.push(s[i] - best);
            i = i + 1;
        }

        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();

    let t: usize = it.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().expect("n").parse().expect("valid n");
        let mut s: Vec<i64> = Vec::with_capacity(n);

        let mut i: usize = 0;
        while i < n {
            s.push(it.next().expect("s_i").parse().expect("valid s_i"));
            i = i + 1;
        }

        let ans = Solution::advantages(s);
        let mut j: usize = 0;
        while j < ans.len() {
            if j > 0 {
                print!(" ");
            }
            print!("{}", ans[j]);
            j = j + 1;
        }
        println!();

        case_id = case_id + 1;
    }
}

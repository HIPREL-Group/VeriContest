use std::io::{self, Read};

struct Solution;

impl Solution {
    fn zero_run_end(s: &Vec<i32>, i: usize) -> usize {
        let n = s.len();
        if i + 1 >= n {
            let j_end = i + 1;
            j_end
        } else {
            if s[i + 1] != 0 {
                let j_end = i + 1;
                j_end
            } else {
                Self::zero_run_end(s, i + 1)
            }
        }
    }

    pub fn min_total_seated_students(s: &Vec<i32>) -> i64 {
        let n = s.len();
        let mut ones: i64 = 0;
        let mut add: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 1 {
                ones = ones + 1;
                i = i + 1;
            } else {
                let j_end = Self::zero_run_end(s, i);
                let l: usize = j_end - i;
                let left: bool = if i > 0 {
                    s[i - 1] == 1
                } else {
                    false
                };
                let right: bool = if j_end < n {
                    s[j_end] == 1
                } else {
                    false
                };
                let extra: i64 = if left && right {
                    (l as i64) / 3
                } else if left || right {
                    ((l as i64) + 1) / 3
                } else {
                    ((l as i64) + 2) / 3
                };
                add = add + extra;
                i = j_end;
            }
        }
        ones + add
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let line: &str = it.next().unwrap();
        let bytes = line.as_bytes();
        let mut s: Vec<i32> = Vec::with_capacity(n);
        let mut k: usize = 0;
        while k < n {
            if bytes[k] == b'0' {
                s.push(0);
            } else {
                s.push(1);
            }
            k = k + 1;
        }
        let ans = Solution::min_total_seated_students(&s);
        println!("{}", ans);
        tc = tc + 1;
    }
}

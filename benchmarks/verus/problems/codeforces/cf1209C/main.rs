use std::io::{self, BufRead};

struct Solution;

impl Solution {
    fn merge_valid(digits: &Vec<i32>, colors: &Vec<i32>, n: usize) -> bool {
        let mut merged: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if colors[i] == 1 {
                merged.push(digits[i]);
            }
            i = i + 1;
        }
        i = 0;
        while i < n {
            if colors[i] == 2 {
                merged.push(digits[i]);
            }
            i = i + 1;
        }
        i = 0;
        while i + 1 < merged.len() {
            if merged[i] > merged[i + 1] {
                return false;
            }
            i = i + 1;
        }
        true
    }

    fn try_pivot(digits: &Vec<i32>, n: usize, x: i32) -> Vec<i32> {
        let mut last_lt: usize = n;
        let mut i: usize = 0;
        while i < n {
            if digits[i] < x {
                last_lt = i;
            }
            i = i + 1;
        }
        let mut colors: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            colors.push(0);
            j = j + 1;
        }
        i = 0;
        while i < n {
            let d = digits[i];
            let c = if d < x {
                1
            } else if d > x {
                2
            } else {
                if last_lt != n && i <= last_lt {
                    2
                } else {
                    1
                }
            };
            colors[i] = c;
            i = i + 1;
        }
        if Solution::merge_valid(digits, &colors, n) {
            colors
        } else {
            vec![]
        }
    }

    pub fn paint_digits(digits: Vec<i32>) -> Vec<i32> {
        let n = digits.len();
        let mut x: i32 = 0;
        while x <= 9 {
            let cand = Solution::try_pivot(&digits, n, x);
            if cand.len() == n {
                return cand;
            }
            x = x + 1;
        }
        vec![]
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut ti = 0usize;
    while ti < t {
        let _n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
        let s = lines.next().unwrap().unwrap();
        let mut digits: Vec<i32> = Vec::new();
        let mut ci = 0usize;
        while ci < s.len() {
            let ch = s.as_bytes()[ci];
            digits.push((ch - b'0') as i32);
            ci = ci + 1;
        }
        let ans = Solution::paint_digits(digits);
        if ans.len() == 0 {
            println!("-");
        } else {
            let mut out = String::new();
            let mut ai = 0usize;
            while ai < ans.len() {
                if ans[ai] == 1 {
                    out.push('1');
                } else {
                    out.push('2');
                }
                ai = ai + 1;
            }
            println!("{}", out);
        }
        ti = ti + 1;
    }
}

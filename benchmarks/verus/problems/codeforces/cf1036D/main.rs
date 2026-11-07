use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_equal_block_count(a: Vec<i64>, b: Vec<i64>) -> i64 {
        let n = a.len();
        let m = b.len();
        let mut ta: i64 = 0;
        let mut tb: i64 = 0;
        let mut u = 0usize;
        while u < n {
            ta = ta + a[u];
            u = u + 1;
        }
        u = 0usize;
        while u < m {
            tb = tb + b[u];
            u = u + 1;
        }
        if ta != tb {
            return -1;
        }
        let mut i = 0usize;
        let mut j = 0usize;
        let mut sa: i64 = 0;
        let mut sb: i64 = 0;
        let mut ans: i64 = 0;
        while i < n || j < m {
            if sa <= sb {
                if i < n {
                    sa = sa + a[i];
                    i = i + 1;
                } else {
                    sb = sb + b[j];
                    j = j + 1;
                }
            } else {
                if j < m {
                    sb = sb + b[j];
                    j = j + 1;
                } else {
                    sa = sa + a[i];
                    i = i + 1;
                }
            }
            if sa == sb && sa > 0 {
                ans = ans + 1;
                sa = 0;
                sb = 0;
            }
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < n {
        let v: i64 = it.next().unwrap().parse().unwrap();
        a.push(v);
        idx = idx + 1;
    }
    let m: usize = it.next().unwrap().parse().unwrap();
    let mut b: Vec<i64> = Vec::new();
    idx = 0usize;
    while idx < m {
        let v: i64 = it.next().unwrap().parse().unwrap();
        b.push(v);
        idx = idx + 1;
    }
    let out = Solution::max_equal_block_count(a, b);
    println!("{}", out);
}

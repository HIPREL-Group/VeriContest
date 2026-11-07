use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_doors_to_lock(l: i32, r: i32, L: i32, R: i32) -> i32 {
        let ma = if l > L {
            l
        } else {
            L
        };
        let mi = if r < R {
            r
        } else {
            R
        };
        let inter = mi - ma + 1;
        if inter <= 0 {
            1
        } else {
            let mut ans: i32 = inter - 1;
            if l != L {
                ans = ans + 1;
            }
            if r != R {
                ans = ans + 1;
            }
            ans
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let l: i32 = it.next().unwrap().parse().unwrap();
        let r: i32 = it.next().unwrap().parse().unwrap();
        let L: i32 = it.next().unwrap().parse().unwrap();
        let R: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::min_doors_to_lock(l, r, L, R);
        println!("{}", ans);
        k = k + 1;
    }
}

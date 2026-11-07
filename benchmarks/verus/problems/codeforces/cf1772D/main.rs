use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn absolute_sorting(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut low: i64 = 0;
        let mut high: i64 = 1000000000;
        let mut i: usize = 0;
        while i + 1 < n {
            let x = a[i] as i64;
            let y = a[i + 1] as i64;
            if x < y {
                let ub = (x + y) / 2;
                if ub < high {
                    high = ub;
                }
            } else if x > y {
                let lb = (x + y + 1) / 2;
                if lb > low {
                    low = lb;
                }
            }
            i += 1;
        }
        if low <= high {
            low as i32
        } else {
            -1
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }
        let ans = Solution::absolute_sorting(a);
        println!("{}", ans);
        case_idx += 1;
    }
}

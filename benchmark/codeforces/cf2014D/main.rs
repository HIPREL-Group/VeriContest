use std::io::{self, Read};

struct Solution;

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn best_start_days(n: i32, d: i32, left: Vec<i32>, right: Vec<i32>) -> (i32, i32) {
        let m = n - d + 1;

        let mm = m as usize;
        let mut diff: Vec<i32> = Vec::with_capacity(mm + 2);
        let mut p: usize = 0;
        while p < mm + 2 {
            diff.push(0);
            p += 1;
        }

        let mut j: usize = 0;
        while j < left.len() {
            let l = left[j];
            let r = right[j];
            let lo = if l - d + 1 > 1 { l - d + 1 } else { 1 };
            let hi = if r < m { r } else { m };
            if lo <= hi {
                let li = lo as usize;
                let hi1 = (hi + 1) as usize;
                diff[li] += 1;
                diff[hi1] -= 1;
            }
            j += 1;
        }

        let mut best_bro: i32 = 1;
        let mut best_mom: i32 = 1;
        let mut best_bro_count: i32 = i32::MIN;
        let mut best_mom_count: i32 = i32::MAX;

        let mut cur: i32 = 0;
        let mut start: usize = 1;
        while start <= mm {
            cur += diff[start];
            if cur > best_bro_count {
                best_bro_count = cur;
                best_bro = start as i32;
            }
            if cur < best_mom_count {
                best_mom_count = cur;
                best_mom = start as i32;
            }
            start += 1;
        }

        (best_bro, best_mom)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match next_i32(&mut it) {
        Some(v) => v as usize,
        None => return,
    };

    let mut out = String::new();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let d: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let k: usize = match next_i32(&mut it) {
            Some(v) => v as usize,
            None => return,
        };

        let mut left: Vec<i32> = Vec::new();
        let mut right: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < k {
            let l: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            let r: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            left.push(l);
            right.push(r);
            i = i + 1;
        }

        let ans = Solution::best_start_days(n, d, left, right);
        out.push_str(&format!("{} {}\n", ans.0, ans.1));

        case_id = case_id + 1;
    }

    print!("{}", out);
}

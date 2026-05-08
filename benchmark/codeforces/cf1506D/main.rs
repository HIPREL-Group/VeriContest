use std::io::{self, Read};

struct Solution;

fn next_usize<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<usize> {
    it.next()?.parse().ok()
}

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn min_remaining_after_epic_transformation(a: Vec<i32>) -> i32 {
        let n: usize = a.len();
        let mut a = a;
        let mut vals = a.clone();
        vals.sort();
        vals.dedup();

        let mut i: usize = 0;
        while i < n {
            let pos = match vals.binary_search(&a[i]) {
                Ok(p) => p,
                Err(_) => 0,
            };
            a[i] = (pos as i32) + 1;
            i = i + 1;
        }

        let mut cnt: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            cnt.push(0);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let v: usize = a[i] as usize;
            cnt[v] = cnt[v] + 1;
            i = i + 1;
        }

        let mut mx: i32 = 0;
        let mut p: usize = 1;
        while p <= n {
            if cnt[p] > mx {
                mx = cnt[p];
            }
            p = p + 1;
        }

        let n_i32: i32 = n as i32;
        let two_mx: i32 = mx + mx;
        if two_mx > n_i32 {
            two_mx - n_i32
        } else {
            n_i32 % 2
        }
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t = match next_usize(&mut it) {
        Some(v) => v,
        None => return,
    };

    let mut case_id: usize = 0;
    while case_id < t {
        let n = match next_usize(&mut it) {
            Some(v) => v,
            None => return,
        };

        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v = match next_i32(&mut it) {
                Some(x) => x,
                None => return,
            };
            a.push(v);
            i = i + 1;
        }

        let ans = Solution::min_remaining_after_epic_transformation(a);
        println!("{}", ans);

        case_id = case_id + 1;
    }
}

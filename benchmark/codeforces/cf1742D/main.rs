use std::io::{self, Read};

struct Solution;

fn next_usize<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<usize> {
    it.next()?.parse().ok()
}

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn is_coprime_values(x: i32, y: i32) -> bool {
        let mut a = x;
        let mut b = y;
        while b != 0 {
            let r = a % b;
            a = b;
            b = r;
        }
        a == 1
    }

    pub fn max_coprime_index_sum(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut last: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 1001 {
            last.push(-1);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let v = a[i] as usize;
            last[v] = i as i32 + 1;
            i = i + 1;
        }

        let mut ans: i32 = -1;
        let mut x: i32 = 1;
        while x <= 1000 {
            let mut y: i32 = 1;
            while y <= 1000 {
                let cop = Self::is_coprime_values(x, y);
                let lx = last[x as usize];
                let ly = last[y as usize];
                if lx != -1 && ly != -1 && cop {
                    let cand = lx + ly;
                    if cand > ans {
                        ans = cand;
                    }
                }
                y = y + 1;
            }
            x = x + 1;
        }

        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match next_usize(&mut it) {
        Some(v) => v,
        None => return,
    };

    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = match next_usize(&mut it) {
            Some(v) => v,
            None => return,
        };

        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i32 = match next_i32(&mut it) {
                Some(x) => x,
                None => return,
            };
            a.push(v);
            i = i + 1;
        }

        let ans = Solution::max_coprime_index_sum(a);
        println!("{}", ans);

        case_id = case_id + 1;
    }
}

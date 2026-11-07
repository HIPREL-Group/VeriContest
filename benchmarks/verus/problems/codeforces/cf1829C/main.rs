use std::io::{self, Read};

struct Solution;

impl Solution {
    fn min_for_mask(m: &Vec<i32>, s: &Vec<i32>, target: i32) -> (i32, bool) {
        let inf: i32 = 1_000_000_000;
        let n = m.len();
        let mut best = inf;
        let mut seen = false;

        let mut i: usize = 0;
        while i < n {
            if s[i] == target {
                if !seen {
                    seen = true;
                    best = m[i];
                } else if m[i] < best {
                    best = m[i];
                }
            }
            i = i + 1;
        }

        (best, seen)
    }

    pub fn min_minutes(m: Vec<i32>, s: Vec<i32>) -> i32 {
        let inf: i32 = 1_000_000_000;
        let n = m.len();

        let r11 = Solution::min_for_mask(&m, &s, 3);
        let r10 = Solution::min_for_mask(&m, &s, 2);
        let r01 = Solution::min_for_mask(&m, &s, 1);

        let best11 = r11.0;
        let seen11 = r11.1;
        let best10 = r10.0;
        let seen10 = r10.1;
        let best01 = r01.0;
        let seen01 = r01.1;

        let cand11 = if seen11 { best11 } else { inf };
        let candpair = if best10 < inf && best01 < inf {
            best10 + best01
        } else {
            inf
        };
        let ans = if cand11 < candpair { cand11 } else { candpair };

        if ans >= inf {
            -1
        } else {
            ans
        }
    }
}

fn parse_mask(bits: &str) -> i32 {
    if bits == "11" {
        3
    } else if bits == "10" {
        2
    } else if bits == "01" {
        1
    } else {
        0
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
        let mut m: Vec<i32> = Vec::with_capacity(n);
        let mut s: Vec<i32> = Vec::with_capacity(n);

        let mut i: usize = 0;
        while i < n {
            let minutes: i32 = it.next().expect("m_i").parse().expect("valid m_i");
            let bits = it.next().expect("s_i");
            m.push(minutes);
            s.push(parse_mask(bits));
            i = i + 1;
        }

        let ans = Solution::min_minutes(m, s);
        println!("{}", ans);
        case_id = case_id + 1;
    }
}

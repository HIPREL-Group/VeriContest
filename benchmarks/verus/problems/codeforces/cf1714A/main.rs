use std::io::{self, Read};

struct Solution;

fn next_usize<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<usize> {
    it.next()?.parse().ok()
}

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn wait_minutes(now: i32, alarm: i32) -> i32 {
        if alarm >= now {
            alarm - now
        } else {
            alarm + 1440 - now
        }
    }

    pub fn min_wait_minutes(now: i32, alarms: Vec<i32>) -> i32 {
        let n = alarms.len();
        let mut best = Self::wait_minutes(now, alarms[0]);
        let mut i: usize = 1;
        while i < n {
            let d = Self::wait_minutes(now, alarms[i]);
            if d < best {
                best = d;
            }
            i = i + 1;
        }
        best
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
        let h: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let m: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let now = h * 60 + m;

        let mut alarms: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let ah: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            let am: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            alarms.push(ah * 60 + am);
            i = i + 1;
        }

        let ans = Solution::min_wait_minutes(now, alarms);
        println!("{} {}", ans / 60, ans % 60);

        case_id = case_id + 1;
    }
}

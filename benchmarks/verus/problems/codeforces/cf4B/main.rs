use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn before_exam_schedule(
        d: usize,
        sum_time: i32,
        min_t: Vec<i32>,
        max_t: Vec<i32>,
    ) -> (bool, Vec<i32>) {
        let mut sum_min: i32 = 0;
        let mut i: usize = 0;
        while i < d {
            sum_min = sum_min + min_t[i];
            i = i + 1;
        }
        let mut sum_max: i32 = 0;
        i = 0;
        while i < d {
            sum_max = sum_max + max_t[i];
            i = i + 1;
        }
        if sum_time < sum_min || sum_time > sum_max {
            return (false, Vec::new());
        }
        let mut rem: i32 = sum_time - sum_min;
        let initial_rem: i32 = rem;
        let mut applied: i32 = 0;
        let mut sched: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < d {
            sched.push(min_t[j]);
            j = j + 1;
        }
        let mut k: usize = 0;
        while k < d {
            let cap: i32 = max_t[k] - min_t[k];
            let add: i32 = if rem > cap { cap } else { rem };
            let new_val: i32 = min_t[k] + add;
            sched[k] = new_val;
            applied = applied + add;
            rem = rem - add;
            k = k + 1;
        }
        (true, sched)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let d: usize = it.next().unwrap().parse().unwrap();
    let sum_time: i32 = it.next().unwrap().parse().unwrap();
    let mut min_t: Vec<i32> = Vec::new();
    let mut max_t: Vec<i32> = Vec::new();
    let mut t: usize = 0;
    while t < d {
        let mn: i32 = it.next().unwrap().parse().unwrap();
        let mx: i32 = it.next().unwrap().parse().unwrap();
        min_t.push(mn);
        max_t.push(mx);
        t = t + 1;
    }
    let (ok, sched) = Solution::before_exam_schedule(d, sum_time, min_t, max_t);
    if ok {
        println!("YES");
        let mut p: usize = 0;
        while p < sched.len() {
            if p > 0 {
                print!(" ");
            }
            print!("{}", sched[p]);
            p = p + 1;
        }
        println!();
    } else {
        println!("NO");
    }
}

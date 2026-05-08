use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_last_exam_day(exams: Vec<(i64, i64)>) -> i64 {
        let mut last_day = exams[0].1;
        let mut i = 1usize;
        while i < exams.len() {
            let a = exams[i].0;
            let b = exams[i].1;
            if b >= last_day {
                last_day = b;
            } else {
                last_day = a;
            }
            i += 1;
        }
        last_day
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut exams: Vec<(i64, i64)> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        exams.push((a, b));
        i += 1;
    }
    exams.sort();
    let answer = Solution::min_last_exam_day(exams);
    println!("{}", answer);
}

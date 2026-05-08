use std::io::{self, Read};

struct Solution;

impl Solution {
    fn is_win_row(row: &Vec<u8>) -> bool {
        let n = row.len();
        let mut j = 0usize;
        let mut found = false;
        while j < n {
            if row[j] == 48u8 {
                found = true;
            }
            j = j + 1;
        }
        found
    }

    pub fn max_consecutive_winning_days(n: usize, d: usize, days: &Vec<Vec<u8>>) -> usize {
        let _ = n;
        let mut best = 0usize;
        let mut cur = 0usize;
        let mut i = 0usize;
        while i < d {
            if Solution::is_win_row(&days[i]) {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut lines = input.lines();
    let first = lines.next().unwrap();
    let mut it = first.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let d: usize = it.next().unwrap().parse().unwrap();
    let mut days: Vec<Vec<u8>> = Vec::new();
    let mut i = 0usize;
    while i < d {
        let line = lines.next().unwrap().trim();
        let mut row: Vec<u8> = Vec::new();
        let mut j = 0usize;
        while j < n {
            row.push(line.as_bytes()[j]);
            j = j + 1;
        }
        days.push(row);
        i = i + 1;
    }
    let mut t = 0usize;
    while t < d {
        assert!(days[t].len() == n);
        t = t + 1;
    }
    let ans = Solution::max_consecutive_winning_days(n, d, &days);
    println!("{}", ans);
}

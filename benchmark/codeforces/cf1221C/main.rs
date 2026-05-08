use std::io;

struct Solution;

impl Solution {
    pub fn max_perfect_teams(c: i64, m: i64, x: i64) -> i64 {
        let s = c + m + x;
        let cap = s / 3;
        let mut r = c;
        if m < r {
            r = m;
        }
        if cap < r {
            r = cap;
        }
        r
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let q: usize = input.trim().parse().unwrap();
    let mut i: usize = 0;
    while i < q {
        let mut line = String::new();
        io::stdin().read_line(&mut line).unwrap();
        let parts: Vec<&str> = line.trim().split_whitespace().collect();
        let c: i64 = parts[0].parse().unwrap();
        let m: i64 = parts[1].parse().unwrap();
        let x: i64 = parts[2].parse().unwrap();
        let ans = Solution::max_perfect_teams(c, m, x);
        println!("{}", ans);
        i = i + 1;
    }
}

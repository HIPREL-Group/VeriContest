use std::io;

struct Solution;

impl Solution {
    pub fn count_bad_prices(a: Vec<i32>) -> i32 {
        let n = a.len();
        if n <= 1 {
            return 0;
        }
        let mut cnt: i32 = 0;
        let mut cur_min = a[n - 1];
        let mut i: usize = n - 2;
        loop {
            if a[i] > cur_min {
                cnt = cnt + 1;
            }
            if a[i] < cur_min {
                cur_min = a[i];
            }
            if i == 0 {
                break;
            }
            i = i - 1;
        }
        cnt
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let t: usize = input.trim().parse().unwrap();
    let mut case_num = 0usize;
    while case_num < t {
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let n: usize = input.trim().parse().unwrap();
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let mut a: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        let parts: Vec<&str> = input.trim().split_whitespace().collect();
        while idx < n {
            let x: i32 = parts[idx].parse().unwrap();
            a.push(x);
            idx += 1;
        }
        let ans = Solution::count_bad_prices(a);
        println!("{}", ans);
        case_num += 1;
    }
}

use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn sort_digits(nums: Vec<u8>) -> Vec<u8> {
        let n = nums.len();
        let mut c1 = 0usize;
        let mut c2 = 0usize;
        let mut c3 = 0usize;
        let mut i = 0usize;
        while i < n {
            if nums[i] == 1 {
                c1 += 1;
            } else if nums[i] == 2 {
                c2 += 1;
            } else {
                c3 += 1;
            }
            i += 1;
        }
        let mut res = Vec::new();
        let mut j = 0usize;
        while j < c1 {
            res.push(1u8);
            j += 1;
        }
        j = 0;
        while j < c2 {
            res.push(2u8);
            j += 1;
        }
        j = 0;
        while j < c3 {
            res.push(3u8);
            j += 1;
        }
        res
    }
}

fn main() {
    let stdin = io::stdin();
    let mut line = String::new();
    stdin.lock().read_line(&mut line).expect("read line");
    let nums: Vec<u8> = line
        .trim()
        .split('+')
        .map(|s| s.parse::<u8>().expect("digit 1, 2, or 3"))
        .collect();
    let sorted = Solution::sort_digits(nums);
    let out: Vec<String> = sorted.into_iter().map(|d| d.to_string()).collect();
    println!("{}", out.join("+"));
}

use std::io;

struct Solution;

impl Solution {
    pub fn max_ones_after_flip(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut result = 0;
        let mut i = 0;
        while i < n {
            let mut j = i;
            while j < n {
                let mut count = 0;
                let mut k = 0;
                while k < n {
                    let val = if i <= k && k <= j {
                        1 - a[k]
                    } else {
                        a[k]
                    };
                    if val == 1 {
                        count = count + 1;
                    }
                    k = k + 1;
                }
                if count > result {
                    result = count;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let n: usize = input.trim().parse().unwrap();
    
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let a: Vec<i32> = input
        .trim()
        .split_whitespace()
        .map(|x| x.parse().unwrap())
        .collect();
    
    let result = Solution::max_ones_after_flip(a);
    println!("{}", result);
}

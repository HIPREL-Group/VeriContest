use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn unique_bid_winner(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut freq: Vec<i32> = Vec::new();
        let mut j = 0usize;
        while j < n + 1 {
            freq.push(0i32);
            j += 1;
        }
        let mut i = 0usize;
        while i < n {
            let vi = a[i] as usize;
            let oldc = freq[vi];
            freq[vi] = oldc + 1;
            i += 1;
        }
        let mut found = false;
        let mut min_val = 0i32;
        let mut v = 1usize;
        while v <= n {
            if freq[v] == 1 {
                if !found || (v as i32) < min_val {
                    min_val = v as i32;
                    found = true;
                }
            }
            v += 1;
        }
        if !found {
            return -1;
        }
        i = 0usize;
        while i < n {
            if a[i] == min_val {
                return (i + 1) as i32;
            }
            i += 1;
        }
        -1
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k = 0usize;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i = 0usize;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }
        let ans = Solution::unique_bid_winner(a);
        println!("{}", ans);
        k += 1;
    }
}

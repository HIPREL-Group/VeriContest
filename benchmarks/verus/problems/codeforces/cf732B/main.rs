use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn cormen_walk_schedule(a: Vec<i32>, k: i32) -> (i64, Vec<i32>) {
        let n = a.len();
        let mut b: Vec<i32> = Vec::new();
        let mut total: i64 = 0;
        let mut prev: i32 = k;
        let mut i: usize = 0;
        while i < n {
            let ai = a[i];
            let kd = k as i64;
            let pred = prev as i64;
            let bi = if (ai as i64) >= kd - pred { ai } else { (kd - pred) as i32 };
            total = total + (bi as i64 - ai as i64);
            b.push(bi);
            prev = bi;
            i = i + 1;
        }
        (total, b)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: i32 = it.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        let x: i32 = it.next().unwrap().parse().unwrap();
        a.push(x);
        j = j + 1;
    }
    let (total, b) = Solution::cormen_walk_schedule(a, k);
    println!("{}", total);
    let mut t: usize = 0;
    while t < b.len() {
        if t > 0 {
            print!(" ");
        }
        print!("{}", b[t]);
        t = t + 1;
    }
    println!();
}

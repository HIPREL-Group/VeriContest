use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn fair_division(n: usize, a: Vec<i32>) -> bool {
        let mut c1: i32 = 0;
        let mut c2: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1 {
                c1 = c1 + 1;
            } else {
                c2 = c2 + 1;
            }
            i = i + 1;
        }
        let total = c1 + 2 * c2;
        if total % 2 != 0 {
            return false;
        }
        let half = total / 2;
        let mut m: i32 = 0;
        while m <= c2 {
            let n1 = half - 2 * m;
            if n1 >= 0 && n1 <= c1 {
                return true;
            }
            m = m + 1;
        }
        false
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut j: usize = 0;
        while j < n {
            a.push(it.next().unwrap().parse().unwrap());
            j = j + 1;
        }
        if Solution::fair_division(n, a) {
            println!("YES");
        } else {
            println!("NO");
        }
        tc = tc + 1;
    }
}

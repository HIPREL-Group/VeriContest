use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn construct_gcd_array(n: usize, l: i32, r: i32) -> (bool, Vec<i32>) {
        let mut a: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t < n {
            a.push(0i32);
            t = t + 1;
        }
        let mut i: usize = 0;
        while i < n {
            let k = (i + 1) as i32;
            let k64 = k as i64;
            let num: i64 = l as i64 + k64 - 1;
            let q = num / k64;
            let first = (q * k64) as i32;
            if first > r {
                return (false, Vec::new());
            }
            a[i] = first;
            i = i + 1;
        }
        (true, a)
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
        let l: i32 = it.next().unwrap().parse().unwrap();
        let r: i32 = it.next().unwrap().parse().unwrap();
        let (ok, a) = Solution::construct_gcd_array(n, l, r);
        if !ok {
            println!("NO");
        } else {
            println!("YES");
            let mut j: usize = 0;
            while j < n {
                if j > 0 {
                    print!(" ");
                }
                print!("{}", a[j]);
                j = j + 1;
            }
            println!();
        }
        tc = tc + 1;
    }
}

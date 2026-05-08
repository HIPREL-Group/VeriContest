use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn is_complementary_xor_possible(a: Vec<i64>, b: Vec<i64>) -> bool {
        let n = a.len();
        let first_xor = if a[0] == b[0] { 0i64 } else { 1i64 };
        let mut i: usize = 1;
        while i < n {
            let cur_xor = if a[i] == b[i] { 0i64 } else { 1i64 };
            if cur_xor != first_xor {
                return false;
            }
            i = i + 1;
        }
        true
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
        let a_str: &str = it.next().unwrap();
        let b_str: &str = it.next().unwrap();
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut b: Vec<i64> = Vec::with_capacity(n);
        let mut j: usize = 0;
        while j < n {
            a.push(if a_str.as_bytes()[j] == b'1' { 1i64 } else { 0i64 });
            b.push(if b_str.as_bytes()[j] == b'1' { 1i64 } else { 0i64 });
            j = j + 1;
        }
        if Solution::is_complementary_xor_possible(a.clone(), b.clone()) {
            println!("YES");
            let mut ops: Vec<(usize, usize)> = Vec::with_capacity(n + 3);
            let first_xor = if a[0] == b[0] { 0i64 } else { 1i64 };
            let mut ones: usize = 0;
            let mut i: usize = 0;
            while i < n {
                if a[i] == 1 {
                    ones = ones + 1;
                    ops.push((i + 1, i + 1));
                }
                i = i + 1;
            }
            let parity = (ones % 2) as i64;
            if parity != first_xor {
                ops.push((1, 1));
                ops.push((2, n));
                ops.push((1, n));
            }
            println!("{}", ops.len());
            let mut k: usize = 0;
            while k < ops.len() {
                println!("{} {}", ops[k].0, ops[k].1);
                k = k + 1;
            }
        } else {
            println!("NO");
        }
        tc = tc + 1;
    }
}

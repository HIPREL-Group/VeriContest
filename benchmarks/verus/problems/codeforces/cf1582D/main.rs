use std::io::{self, Read};

struct Solution;

fn next_usize<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<usize> {
    it.next()?.parse().ok()
}

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn construct_coeffs(a: Vec<i32>) -> Vec<i32> {
        let n = a.len();
        let mut b: Vec<i32> = Vec::new();

        if n % 2 == 1 {
            let x0 = a[0];
            let x1 = a[1];
            let x2 = a[2];
            if x0 + x1 != 0 {
                b.push(x2);
                b.push(x2);
                b.push(-(x0 + x1));
            } else if x0 + x2 != 0 {
                b.push(x1);
                b.push(-(x0 + x2));
                b.push(x1);
            } else {
                b.push(-(x1 + x2));
                b.push(x0);
                b.push(x0);
            }

            let mut i: usize = 3;
            while i < n {
                b.push(a[i + 1]);
                b.push(-a[i]);
                i = i + 2;
            }
        } else {
            let mut i: usize = 0;
            while i < n {
                b.push(a[i + 1]);
                b.push(-a[i]);
                i = i + 2;
            }
        }

        b
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match next_usize(&mut it) {
        Some(v) => v,
        None => return,
    };

    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = match next_usize(&mut it) {
            Some(v) => v,
            None => return,
        };

        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v = match next_i32(&mut it) {
                Some(x) => x,
                None => return,
            };
            a.push(v);
            i = i + 1;
        }

        let b = Solution::construct_coeffs(a);
        let mut j: usize = 0;
        while j < b.len() {
            if j > 0 {
                print!(" ");
            }
            print!("{}", b[j]);
            j = j + 1;
        }
        println!();

        case_id = case_id + 1;
    }
}

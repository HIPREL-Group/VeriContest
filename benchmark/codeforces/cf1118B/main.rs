use std::io;

struct Solution;

impl Solution {
    pub fn count_equal_sums(a: Vec<i64>) -> i32 {
        let n = a.len();
        let mut total_even_idx = 0i64;
        let mut total_odd_idx = 0i64;
        let mut t = 0;
        while t < n {
            if t % 2 == 0 {
                total_even_idx = total_even_idx + a[t];
            } else {
                total_odd_idx = total_odd_idx + a[t];
            }
            t = t + 1;
        }
        let mut po = 0i64;
        let mut pe = 0i64;
        let mut count = 0i32;
        let mut i = 0;
        while i < n {
            let odd_tail = total_odd_idx - pe - if i % 2 == 1 { a[i] } else { 0 };
            let even_tail = total_even_idx - po - if i % 2 == 0 { a[i] } else { 0 };
            let odd_sum = po + odd_tail;
            let even_sum = pe + even_tail;
            if odd_sum == even_sum {
                count = count + 1;
            }
            if i % 2 == 0 {
                po = po + a[i];
            } else {
                pe = pe + a[i];
            }
            i = i + 1;
        }
        count
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let _n: usize = input.trim().parse().unwrap();

    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let a: Vec<i64> = input
        .trim()
        .split_whitespace()
        .map(|x| x.parse().unwrap())
        .collect();

    println!("{}", Solution::count_equal_sums(a));
}

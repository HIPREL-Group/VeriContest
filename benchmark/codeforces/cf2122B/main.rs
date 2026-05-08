use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_pile_shuffle_operations(a: &Vec<i64>, b: &Vec<i64>, c: &Vec<i64>, d: &Vec<i64>) -> i64 {
        let n = a.len();
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut av: i64 = a[i];
            let bv: i64 = b[i];
            let cv: i64 = c[i];
            let dv: i64 = d[i];
            if av > cv {
                ans = ans + (av - cv);
                av = cv;
            }
            if bv > dv {
                ans = ans + (bv - dv + av);
            }
            i = i + 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut b: Vec<i64> = Vec::new();
        let mut c: Vec<i64> = Vec::new();
        let mut d: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let ai: i64 = it.next().unwrap().parse().unwrap();
            let bi: i64 = it.next().unwrap().parse().unwrap();
            let ci: i64 = it.next().unwrap().parse().unwrap();
            let di: i64 = it.next().unwrap().parse().unwrap();
            a.push(ai);
            b.push(bi);
            c.push(ci);
            d.push(di);
            j = j + 1;
        }
        let ans = Solution::min_pile_shuffle_operations(&a, &b, &c, &d);
        println!("{}", ans);
        k = k + 1;
    }
}

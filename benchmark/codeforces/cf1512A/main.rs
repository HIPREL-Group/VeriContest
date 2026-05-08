use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn spy_index(a: Vec<i64>) -> usize {
        let n = a.len();
        if a[0] != a[1] {
            if a[0] == a[2] {
                return 2;
            } else {
                return 1;
            }
        }

        let mut i: usize = 2;
        while i < n {
            if a[i] != a[0] {
                return i + 1;
            }
            i += 1;
        }

        1
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a = Vec::with_capacity(n);
        for _ in 0..n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let ans = Solution::spy_index(a);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}

use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_cost_make_equal(a: Vec<i64>) -> i64 {
        let n: usize = a.len();

        let mut left: usize = 0;
        while left < n && a[left] == a[0] {
            left += 1;
        }

        let mut right: usize = 0;
        while right < n && a[n - 1 - right] == a[n - 1] {
            right += 1;
        }

        let mut ans: usize = if n - left <= n - right { n - left } else { n - right };
        if a[0] == a[n - 1] {
            let keep = if left + right <= n { left + right } else { n };
            ans = n - keep;
        }

        let out = ans as i64;
        out
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
        let mut a: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let ans = Solution::min_cost_make_equal(a);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}

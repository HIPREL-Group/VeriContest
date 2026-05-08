use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn steps_from_diff(d: i64) -> i64 {
        if d == 0 {
            0
        } else {
            let sub = Self::steps_from_diff(d / 2);
            sub + 1
        }
    }

    pub fn min_operations(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut i: usize = 1;
        while i < n {
            let cur = a[i];
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            i += 1;
        }
        Self::steps_from_diff(mx - mn)
    }

    pub fn build_operations(mut mn: i64, mut mx: i64, steps: i64) -> Vec<i64> {
        let mut ops: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < steps {
            let x = if mn % 2 == 1 && mx % 2 == 0 { 1 } else { 0 };
            ops.push(x);
            mn = (mn + x) / 2;
            mx = (mx + x) / 2;
            i += 1;
        }
        ops
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
        let mut mn: i64 = 1_000_000_000;
        let mut mx: i64 = 0;

        for _ in 0..n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            if v < mn {
                mn = v;
            }
            if v > mx {
                mx = v;
            }
            a.push(v);
        }

        let k = Solution::min_operations(a);
        out.push_str(&format!("{}\n", k));

        if k <= n as i64 {
            let ops = Solution::build_operations(mn, mx, k);
            if !ops.is_empty() {
                for i in 0..ops.len() {
                    if i > 0 {
                        out.push(' ');
                    }
                    out.push_str(&ops[i].to_string());
                }
            }
            out.push('\n');
        }
    }

    print!("{}", out);
}

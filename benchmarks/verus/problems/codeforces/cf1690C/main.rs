use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn restore_durations(s: Vec<i64>, f: Vec<i64>) -> Vec<i64> {
        let n = s.len();
        let mut result: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            let start = if i == 0 || s[i] > f[i - 1] { s[i] } else { f[i - 1] };
            let dur = f[i] - start;
            result.push(dur);
            i = i + 1;
        }
        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case: usize = 0;
    while case < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");
        let mut s: Vec<i64> = Vec::with_capacity(n);
        let mut f: Vec<i64> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            s.push(tokens.next().expect("s").parse().expect("valid"));
            idx = idx + 1;
        }
        idx = 0;
        while idx < n {
            f.push(tokens.next().expect("f").parse().expect("valid"));
            idx = idx + 1;
        }
        let result = Solution::restore_durations(s, f);
        let mut out = String::new();
        idx = 0;
        while idx < n {
            if idx > 0 {
                out.push(' ');
            }
            out.push_str(&result[idx].to_string());
            idx = idx + 1;
        }
        println!("{}", out);
        case = case + 1;
    }
}

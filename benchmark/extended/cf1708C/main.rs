use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn optimal_tests(a: Vec<i64>, q: i64) -> Vec<u8> {
        let n = a.len();
        let mut cur_q: i64 = 0;
        let mut ans: Vec<u8> = Vec::new();
        let mut fill: usize = 0;
        while fill < n {
            ans.push(0);
            fill = fill + 1;
        }

        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let aval = a[i];

            if aval <= cur_q {
                ans[i] = 1;
            } else if cur_q < q {
                cur_q = cur_q + 1;
                ans[i] = 1;
            } else {
                ans[i] = 0;
            }
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    if let Some(t_str) = tokens.next() {
        let t: usize = t_str.parse().expect("t");
        for _ in 0..t {
            if let Some(n_str) = tokens.next() {
                let n: usize = n_str.parse().expect("n");
                let q: i64 = tokens.next().expect("q").parse().expect("q");
                let mut a = Vec::with_capacity(n);
                let mut i = 0;
                while i < n {
                    a.push(tokens.next().expect("a").parse().expect("a"));
                    i += 1;
                }
                
                let ans = Solution::optimal_tests(a, q);
                let mut ans_str = String::new();
                for b in ans {
                    ans_str.push_str(&b.to_string());
                }
                println!("{}", ans_str);
            }
        }
    }
}

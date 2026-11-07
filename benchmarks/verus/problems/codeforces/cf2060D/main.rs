use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_sort(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut cur: i64 = a[0];
        let mut i: usize = 0;
        while i < n - 1 {
            let next = a[i + 1];
            if cur > next {
                return false;
            }
            let new_cur = next - cur;
            cur = new_cur;
            i = i + 1;
        }
        true
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
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            a.push(tokens.next().expect("element").parse().expect("valid i64"));
            idx = idx + 1;
        }
        if Solution::can_sort(a) {
            println!("YES");
        } else {
            println!("NO");
        }
        case = case + 1;
    }
}

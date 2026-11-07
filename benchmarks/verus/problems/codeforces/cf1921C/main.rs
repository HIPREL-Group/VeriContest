use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_send_all_messages(m: Vec<i64>, f: i64, a: i64, b: i64) -> bool {
        let n = m.len();
        let mut spent: i64 = 0;
        let mut prev: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let cur = m[i];
            let gap = m[i] - prev;
            let keep = gap * a;
            let step = if keep < b { keep } else { b };
            spent = spent + step;
            prev = m[i];
            i = i + 1;
        }
        spent < f
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let t: usize = it.next().expect("t").parse().expect("t");

    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().expect("n").parse().expect("n");
        let f: i64 = it.next().expect("f").parse().expect("f");
        let a: i64 = it.next().expect("a").parse().expect("a");
        let b: i64 = it.next().expect("b").parse().expect("b");

        let mut m: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            m.push(it.next().expect("m").parse().expect("m"));
            i = i + 1;
        }

        let ok = Solution::can_send_all_messages(m, f, a, b);
        if ok {
            println!("YES");
        } else {
            println!("NO");
        }
        case_idx = case_idx + 1;
    }
}

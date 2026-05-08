use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn fair_playoff(s1: i64, s2: i64, s3: i64, s4: i64) -> bool {
        let w1 = if s1 >= s2 { s1 } else { s2 };
        let w2 = if s3 >= s4 { s3 } else { s4 };
        let l1 = if s1 <= s2 { s1 } else { s2 };
        let l2 = if s3 <= s4 { s3 } else { s4 };
        let weaker_winner = if w1 <= w2 { w1 } else { w2 };
        let stronger_loser = if l1 >= l2 { l1 } else { l2 };
        weaker_winner > stronger_loser
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case_idx: usize = 0;
    while case_idx < t {
        let s1: i64 = tokens.next().expect("s1").parse().expect("valid s1");
        let s2: i64 = tokens.next().expect("s2").parse().expect("valid s2");
        let s3: i64 = tokens.next().expect("s3").parse().expect("valid s3");
        let s4: i64 = tokens.next().expect("s4").parse().expect("valid s4");
        if Solution::fair_playoff(s1, s2, s3, s4) {
            println!("YES");
        } else {
            println!("NO");
        }
        case_idx += 1;
    }
}

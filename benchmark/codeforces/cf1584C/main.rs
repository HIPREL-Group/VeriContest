use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_transform(a: Vec<i32>, b: Vec<i32>) -> bool {
        let n = a.len();
        let mut carry: i64 = 0;
        let mut val: i32 = -100;

        while val <= 100 {
            let mut av: usize = 0;
            let mut vi: usize = 0;
            while vi < n {
                if a[vi] == val {
                    av = av + 1;
                }
                vi = vi + 1;
            }

            let mut bv: usize = 0;
            vi = 0;
            while vi < n {
                if b[vi] == val {
                    bv = bv + 1;
                }
                vi = vi + 1;
            }

            let next = av as i64 - bv as i64 + carry;
            if next < 0 || next > av as i64 {
                return false;
            }

            carry = next;
            val = val + 1;
        }

        carry == 0
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();

    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");

        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(tokens.next().expect("a_i").parse().expect("valid a_i"));
            i = i + 1;
        }

        let mut b: Vec<i32> = Vec::with_capacity(n);
        i = 0;
        while i < n {
            b.push(tokens.next().expect("b_i").parse().expect("valid b_i"));
            i = i + 1;
        }

        if Solution::can_transform(a, b) {
            println!("YES");
        } else {
            println!("NO");
        }

        case_id = case_id + 1;
    }
}

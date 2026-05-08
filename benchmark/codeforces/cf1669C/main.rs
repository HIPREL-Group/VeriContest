use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_make_same_parity(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut i: usize = 0;
        while i < n {
            if a[i] % 2 != a[0] % 2 {
                return false;
            }
            i = i + 2;
        }

        if n >= 2 {
            let mut j: usize = 1;
            while j < n {
                if a[j] % 2 != a[1] % 2 {
                    return false;
                }
                j = j + 2;
            }
        }

        true
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }

        if Solution::can_make_same_parity(a) {
            println!("YES");
        } else {
            println!("NO");
        }

        tc = tc + 1;
    }
}